// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// A StormTracker wraps a LocalCMC, and prevents KMS storms
//
// NOT an ICryptographicMaterialsCache, because it implements GetFromCache
// instead of GetCacheEntry, to distinguish 'no data so sleep' from 'no data so get some'
//
// If an item in the cache is about to expire, return occasional 'data not found'
// so that the cache can be refreshed before all the threads suddenly need data
// giving all other threads the cached data
//
// If an item is not in the cache, return occasional 'data not found'
// so that the cache can be refreshed,
// forcing all other threads to sleep

include "LocalCMC.dfy"

module {:options "/functionSyntax:4" }  StormTracker {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened DafnyLibraries
  import Types = AwsCryptographyMaterialProvidersTypes
  import LocalCMC
  import Time
  import SortedSets

  datatype CacheState =
    | EmptyWait // No data, client should wait
    | EmptyFetch // No data, client should fetch
    | Full(data : Types.GetCacheEntryOutput)

  class StormTracker {

    ghost predicate ValidState()
      reads this, wrapped, wrapped.Modifies
    {
      && this !in wrapped.Modifies
      && inFlight !in wrapped.Modifies
      && wrapped.ValidState()
    }
    var wrapped : LocalCMC.LocalCMC; // the actual cache
    var inFlight: MutableMap<seq<uint8>, Types.PositiveLong> // the time at which this key became in flight
    var gracePeriod : Types.PositiveLong // seconds before expiration that we start putting things in flight
    var graceInterval : Types.PositiveLong // minimum seconds before putting the same key in flight again
    var fanOut : Types.PositiveLong // maximum keys in flight at one time
    var inFlightTTL : Types.PositiveLong // maximum time before a key is no longer in flight

    constructor(
      entryCapacity: nat,
      entryPruningTailSize: nat := 1,
      gracePeriod : Types.PositiveLong := 10,
      graceInterval : Types.PositiveLong := 1,
      fanOut : Types.PositiveLong := 20,
      inFlightTTL : Types.PositiveLong := 5
    )
      requires entryPruningTailSize >= 1
      ensures
        && this.ValidState()
        && fresh(this.wrapped)
        && fresh(this.wrapped.Modifies)
        && fresh(this.inFlight)
    {
      this.wrapped := new LocalCMC.LocalCMC(entryCapacity, entryPruningTailSize);
      this.inFlight := new MutableMap();
      this.gracePeriod := gracePeriod;
      this.graceInterval := graceInterval;
      this.fanOut := fanOut;
      this.inFlightTTL := inFlightTTL;
    }

    function InFlightSize() : Types.PositiveLong
      reads this, this.inFlight
    {
      var x := inFlight.Size();
      assert x >= 0;
      if x <= INT64_MAX_LIMIT then
        x as Types.PositiveLong
      else
        INT64_MAX_LIMIT as Types.PositiveLong
    }

    function AddLong(x : Types.PositiveLong, y : Types.PositiveLong) : Types.PositiveLong
    {
      if x < (INT64_MAX_LIMIT as Types.PositiveLong - y) then
        x + y
      else
        INT64_MAX_LIMIT as Types.PositiveLong
    }

    // If entry is within `grace time` of expiration, then return EmptyFetch once per `grace interval`, 
    // and return cached value otherwise
    method CheckInFlight(identifier: seq<uint8>, result: Types.GetCacheEntryOutput, now : Types.PositiveLong)
      returns (output: CacheState)
      modifies inFlight
    {
      if fanOut <= InFlightSize() {
        return Full(result);
      } else if result.expiryTime <= now { // expired? should be impossible
        output := CheckNewEntry(identifier, now);
      } else if now < result.expiryTime - gracePeriod { // lots of time left
        return Full(result);
      } else { // in grace time
        if inFlight.HasKey(identifier) {
          var entry := inFlight.Select(identifier);
          if AddLong(entry, graceInterval) > now {  // already returned an EmptyFetch for this interval
            return Full(result);
          }
        }
        inFlight.Put(identifier, now);
        return EmptyFetch;
      }
    }

    // If InFlight is at maximum, see if any entries are too old
    method PruneInFlight(now : Types.PositiveLong)
      modifies inFlight
    {
      if fanOut > InFlightSize() {
        return;
      }
      var keySet := inFlight.Keys();
      var keys := SortedSets.ComputeSetToSequence(keySet);
      for i := 0 to |keys| {
        var v := inFlight.Select(keys[i]);
        if now >= AddLong(v, inFlightTTL) {
          inFlight.Remove(keys[i]);
          return;
        }
      }
    }
    // If entry is not in cache, then return EmptyFetch once per second, and EmptyWait otherwise
    method CheckNewEntry(identifier: seq<uint8>, now : Types.PositiveLong)
      returns (output: CacheState)
      modifies inFlight
    {
      if fanOut <= InFlightSize() {
        return EmptyWait;
      } else if inFlight.HasKey(identifier) {
        var entry := inFlight.Select(identifier);
        if AddLong(entry, graceInterval) > now {  // already returned an EmptyFetch for this interval
          return EmptyWait;
        }
      }
      inFlight.Put(identifier, now);
      return EmptyFetch;
    }

    // Pass in timestamp for easier testing
    method GetFromCacheWithTime(input: Types.GetCacheEntryInput, now : Types.PositiveLong)
      returns (output: Result<CacheState, Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
      ensures inFlight == old(inFlight)
      ensures wrapped == old(wrapped)
      ensures wrapped.Modifies <= old(wrapped.Modifies)
    {
      PruneInFlight(now);
      var result := wrapped.GetCacheEntryWithTime(input, now);
      if result.Success? {
        var newResult := CheckInFlight(input.identifier, result.value, now);
        return Success(newResult);
      } else if result.error.EntryDoesNotExist? {
        var newResult := CheckNewEntry(input.identifier, now);
        return Success(newResult);
      } else {
        return Failure(result.error);
      }
    }

    method GetFromCache(input: Types.GetCacheEntryInput)
      returns (output: Result<CacheState, Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
      ensures inFlight == old(inFlight)
      ensures wrapped == old(wrapped)
      ensures wrapped.Modifies <= old(wrapped.Modifies)
    {
      var now := Time.GetCurrent();
      output := GetFromCacheWithTime(input, now);
    }

    // This should not be used directly.
    // If we needed StormTracker to be an ICryptographicMaterialsCache, this would be needed
    // It is also useful because Dafny generates almost the right code for the native StormTrackingCMC
    method GetCacheEntry(input: Types.GetCacheEntryInput)
      returns (output: Result<Types.GetCacheEntryOutput, Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
      ensures inFlight == old(inFlight)
      ensures wrapped == old(wrapped)
      ensures wrapped.Modifies <= old(wrapped.Modifies)
    {
      var result := GetFromCache(input);
      if result.Failure? {
        return Failure(result.error);
      } else if result.value.Full? {
        return Success(result.value.data);
      } else {
        return Failure(Types.EntryDoesNotExist(message := "Entry does not exist"));
      }
    }

    method PutCacheEntry(input: Types.PutCacheEntryInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
      ensures inFlight == old(inFlight)
      ensures wrapped == old(wrapped)
      ensures fresh(wrapped.Modifies - old(wrapped.Modifies))
    {
      inFlight.Remove(input.identifier);
      output := wrapped.PutCacheEntry'(input);
    }

    method DeleteCacheEntry(input: Types.DeleteCacheEntryInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
      ensures wrapped.Modifies <= old(wrapped.Modifies)
    {
      inFlight.Remove(input.identifier);
      output := wrapped.DeleteCacheEntry'(input);
    }

    method UpdaterUsageMetadata(input: Types.UpdaterUsageMetadataInput)
      returns (output: Result<(), Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
    {
      output := wrapped.UpdaterUsageMetadata'(input);
    }
  }
}
