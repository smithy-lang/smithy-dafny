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
  }
}
