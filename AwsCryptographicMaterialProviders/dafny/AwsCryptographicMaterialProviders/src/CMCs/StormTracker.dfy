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

  datatype CacheState =
    | EmptyWait // No data, client should wait
    | EmptyFetch // No data, client should fetch
    | Full(data : Types.GetCacheEntryOutput)

  class StormTracker {

    ghost predicate ValidState()
      reads this, wrapped, wrapped.Modifies
    {
      // && this in Modifies
      // && wrapped in Modifies
      // && inFlight in Modifies
      // && wrapped.Modifies <= Modifies
      && this !in wrapped.Modifies
      && inFlight !in wrapped.Modifies
      && wrapped.ValidState()
    }
    var wrapped : LocalCMC.LocalCMC;
    var inFlight: MutableMap<seq<uint8>, Types.PositiveLong>
    // ghost var Modifies : set<object>

    constructor(
      entryCapacity: nat,
      entryPruningTailSize: nat := 1
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
      // new;
      // Modifies := { wrapped, inFlight, this } + wrapped.Modifies;
    }

    ghost function Modifies() : set<object>
      reads this, wrapped, wrapped.Modifies
    {
      {inFlight} + wrapped.Modifies
    }

    // If entry is within 10 seconds of expiration, then return EmptyFetch once per second, 
    // and return cached value otherwise
    method CheckInFlight(identifier: seq<uint8>, result: Types.GetCacheEntryOutput, now : Types.PositiveLong)
      returns (output: CacheState)
      modifies inFlight
    {
      if result.expiryTime <= now { // should be impossible
        return Full(result);
      } else if now < result.expiryTime - 10 { // lots of time left
        return Full(result);
      } else { // in grace time
        var timeLeft : Types.PositiveLong := result.expiryTime - now;
        assert 0 < timeLeft <= 10;
        if inFlight.HasKey(identifier) {
          var entry := inFlight.Select(identifier);
          if entry <= timeLeft {  // already returned a EmptyFetch for this second
            return Full(result);
          }
        }
        inFlight.Put(identifier, timeLeft);
        return EmptyFetch;
      }
    }

    // If entry is not in cache, then return EmptyFetch once per second, and EmptyWait otherwise
    method CheckNewEntry(identifier: seq<uint8>, now : Types.PositiveLong)
      returns (output: CacheState)
      modifies inFlight
    {
      if inFlight.HasKey(identifier) {
        var entry := inFlight.Select(identifier);
        if entry == now {  // already returned a EmptyFetch for this second
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

    /*
    // If StormTracker wanted to implement GetCacheEntry, this is what it would look like.
    method GetCacheEntry(input: Types.GetCacheEntryInput)
      returns (output: Result<Types.GetCacheEntryOutput, Types.Error>)
      requires ValidState()
      modifies inFlight, wrapped.Modifies
      ensures ValidState()
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
    */

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
