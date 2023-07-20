// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../../src/Index.dfy"
include "../TestUtils.dfy"

module  {:options "/functionSyntax:4"} TestLocalCMC {
  import opened AwsCryptographyMaterialProvidersTypes
  import opened UInt = StandardLibrary.UInt
  import opened Wrappers
  import opened LocalCMC
  import opened AwsCryptographyKeyStoreTypes
  import UTF8

  function MakeMat(data : Utf8Bytes) : Materials
  {
    BranchKey(BranchKey := BranchKeyMaterials (
                branchKeyIdentifier := "spoo",
                branchKeyVersion := data,
                branchKey := data,
                encryptionContext := map[]
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

  method {:test} LocalCMCBasics() {
    var st := new LocalCMC(100);

    var abc := UTF8.EncodeAscii("abc");
    var cde := UTF8.EncodeAscii("cde");
    var res := st.GetCacheEntryWithTime(MakeGet(abc), 10000);
    expect res.Failure?;
    expect res.error.EntryDoesNotExist?;

    var res2 :- expect st.PutCacheEntry'(MakePut(abc, 10000));
    res2 :- expect st.PutCacheEntry'(MakePut(cde, 10000));

    var res3 :- expect st.GetCacheEntryWithTime(MakeGet(abc), 9999);
    res3 :- expect st.GetCacheEntryWithTime(MakeGet(abc), 10000);
    res := st.GetCacheEntryWithTime(MakeGet(abc), 10001);
    expect res.Failure?;
    expect res.error.EntryDoesNotExist?;

    res3 :- expect st.GetCacheEntryWithTime(MakeGet(cde), 9999);
    var res5 :- expect st.DeleteCacheEntry'(MakeDel(cde));
    res := st.GetCacheEntryWithTime(MakeGet(abc), 9999);
    expect res.Failure?;
    expect res.error.EntryDoesNotExist?;
    res5 :- expect st.DeleteCacheEntry'(MakeDel(cde));
  }
}
