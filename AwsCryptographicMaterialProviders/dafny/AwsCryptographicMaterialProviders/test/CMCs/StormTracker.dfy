// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/Index.dfy"
include "../TestUtils.dfy"

module  {:options "/functionSyntax:4"} TestStormTracker {
  import opened AwsCryptographyMaterialProvidersTypes
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import opened StormTracker
  import UTF8

  function MakeMat(data : Utf8Bytes) : Materials
  {
    BranchKey(BranchKey := BranchKeyMaterials (
                branchKeyVersion := data,
                branchKey := data
              ))
  }

  function MakeGet(data : Utf8Bytes) : GetCacheEntryInput
  {
    GetCacheEntryInput (
      identifier := data,
      bytesUsed := Option.None
    )
  }
  function MakeDel(data : Utf8Bytes) : DeleteCacheEntryInput
  {
    DeleteCacheEntryInput (
      identifier := data
    )
  }
  function MakePut(data : Utf8Bytes, expiryTime : PositiveLong) : PutCacheEntryInput
  {
    PutCacheEntryInput (
      identifier := data,
      materials := MakeMat(data),
      creationTime := 123456789,
      expiryTime := expiryTime,
      messagesUsed := Option.None,
      bytesUsed := Option.None
    )
  }

  method {:test} StormTrackerBasics() {
    var st := new StormTracker(100);

    var abc := UTF8.EncodeAscii("abc");
    var cde := UTF8.EncodeAscii("cde");
    var res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10000);
    expect res.EmptyWait?;
    var res2 :- expect st.PutCacheEntry(MakePut(abc, 10000));
    res2 :- expect st.PutCacheEntry(MakePut(cde, 10000));
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10001);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(abc), 10001);
    expect res.EmptyWait?;

    // the following are to test the Dafny header, to see that it allows for multiple calls
    var res3 := st.GetCacheEntry(MakeGet(abc));
    res3 := st.GetCacheEntry(MakeGet(abc));
    var res4 := st.GetFromCache(MakeGet(abc));
    res4 := st.GetFromCache(MakeGet(abc));
    var res5 := st.DeleteCacheEntry(MakeDel(abc));
    res5 := st.DeleteCacheEntry(MakeDel(abc));
  }

  method {:test} StormTrackerFanOut()
  {
    var st := new StormTracker(
      entryCapacity := 100,
      entryPruningTailSize := 1,
      gracePeriod := 10,
      graceInterval := 1,
      fanOut := 3
    );

    var one := UTF8.EncodeAscii("one");
    var two := UTF8.EncodeAscii("two");
    var three := UTF8.EncodeAscii("three");
    var four := UTF8.EncodeAscii("four");

    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(two), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(three), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10000);
    expect res.EmptyWait?;
  }

    method {:test} StormTrackerTTL()
  {
    var st := new StormTracker(
      entryCapacity := 100,
      entryPruningTailSize := 1,
      gracePeriod := 10,
      graceInterval := 1,
      fanOut := 3,
      inFlightTTL := 5
    );

    var one := UTF8.EncodeAscii("one");
    var two := UTF8.EncodeAscii("two");
    var three := UTF8.EncodeAscii("three");
    var four := UTF8.EncodeAscii("four");

    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(two), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(three), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10000);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10001);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10003);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(four), 10005);
    expect res.EmptyFetch?;
  }

  method {:test} StormTrackerGraceInterval()
  {
    var st := new StormTracker(
      entryCapacity := 100,
      entryPruningTailSize := 1,
      gracePeriod := 10,
      graceInterval := 3,
      fanOut := 10
    );

    var one := UTF8.EncodeAscii("one");

    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10001);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10002);
    expect res.EmptyWait?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10003);
    expect res.EmptyFetch?;
  }

  method {:test} StormTrackerGracePeriod()
  {
    var st := new StormTracker(
      entryCapacity := 100,
      entryPruningTailSize := 1,
      gracePeriod := 10,
      graceInterval := 3,
      fanOut := 10
    );

    var one := UTF8.EncodeAscii("one");

    var res2 :- expect st.PutCacheEntry(MakePut(one, 10010));

    var res :- expect st.GetFromCacheWithTime(MakeGet(one), 9999);
    expect res.Full?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.EmptyFetch?;
    res :- expect st.GetFromCacheWithTime(MakeGet(one), 10000);
    expect res.Full?;
  }
}
