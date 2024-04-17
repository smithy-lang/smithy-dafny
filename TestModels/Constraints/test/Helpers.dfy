// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module Helpers {
  import SimpleConstraints
  import opened StandardLibrary.UInt
  import opened SimpleConstraintsTypes
  import opened Wrappers

  // UTF-8 encoded "aws-kms"
  const PROVIDER_ID: UTF8.ValidUTF8Bytes :=
    var s := [0x61, 0x77, 0x73, 0x2D, 0x6B, 0x6D, 0x73];
    assert UTF8.ValidUTF8Range(s, 0, 7);
    s


  // This returns a valid GetConstraintsInput object.
  function method GetValidInput() : GetConstraintsInput
  {
    // var myComplexUniqueList :=
    //   [ ComplexListElement(value := Some("one"), blob := Some([1, 1])),
    //     ComplexListElement(value := Some("two"), blob := Some([2, 2]))
    //   ];

    GetConstraintsInput(
      MyString := Some("bw1and10"),
      NonEmptyString := Some("atleast1"),
      StringLessThanOrEqualToTen := Some("leq10"),
      MyBlob := Some([0, 1, 0, 1]),
      NonEmptyBlob := Some( [0, 1, 0, 1]),
      BlobLessThanOrEqualToTen := Some([0, 1, 0, 1]),
      MyList := Some(["00", "11"]),
      NonEmptyList := Some(["00", "11"]),
      ListLessThanOrEqualToTen := Some(["00", "11"]),
      MyMap := Some(map["0" := "1", "2" := "3"]),
      NonEmptyMap := Some(map["0" := "1", "2" := "3"]),
      MapLessThanOrEqualToTen := Some(map["0" := "1", "2" := "3"]),
      // Alphabetic := Some("alphabetic"),
      OneToTen := Some(3),
      myTenToTen := Some(3),
      GreaterThanOne := Some(3),
      LessThanTen := Some(3),
      // MyUniqueList := Some(["one", "two"]),
      // MyComplexUniqueList := Some(myComplexUniqueList),
      MyUtf8Bytes := Some(PROVIDER_ID),
      MyListOfUtf8Bytes := Some([PROVIDER_ID, PROVIDER_ID])
    )
  }

  predicate method ValidInt32(x : int)
  {
    -0x8000_0000 <= x < 0x8000_0000
  }

  predicate method ValidInt64(x : int)
  {
    -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
  }

  function method ForceUtf8Bytes(value : seq<uint8>) : Utf8Bytes
  {
    assume {:axiom} UTF8.ValidUTF8Seq(value);
    assume {:axiom} IsValid_Utf8Bytes(value);
    var myUtf8Bytes: Utf8Bytes := value;
    myUtf8Bytes
  }
  
  function method ForceListOfUtf8Bytes(value : seq<Utf8Bytes>) : ListOfUtf8Bytes
  {
    assume {:axiom} IsValid_ListOfUtf8Bytes(value);
    var myListOfUtf8Bytes: ListOfUtf8Bytes := value;
    myListOfUtf8Bytes
  }

  function method ForceLessThanTen(value : int) : LessThanTen
  {
    assume {:axiom} ValidInt32(value);
    var v32 := value as int32;
    assume {:axiom} IsValid_LessThanTen(v32);
    var myLessThanTen: LessThanTen := v32;
    myLessThanTen
  }

  function method ForceOneToTen(value : int) : OneToTen
  {
    assume {:axiom} ValidInt32(value);
    var v32 := value as int32;
    assume {:axiom} IsValid_OneToTen(v32);
    var myOneToTen: OneToTen := v32;
    myOneToTen
  }

  function method ForceTenToTen(value : int) : TenToTen
  {
    assume {:axiom} ValidInt64(value);
    var v64 := value as int64;
    assume {:axiom} IsValid_TenToTen(v64);
    var myTenToTen: TenToTen := v64;
    myTenToTen
  }

  function method ForceMyString(value : string) : MyString
  {
    assume {:axiom} IsValid_MyString(value);
    var myMyString: MyString := value;
    myMyString
  }

  function method ForceNonEmptyString(value : string) : NonEmptyString
  {
    assume {:axiom} IsValid_NonEmptyString(value);
    var myNonEmptyString: NonEmptyString := value;
    myNonEmptyString
  }

  function method ForceStringLessThanOrEqualToTen(value : string) : StringLessThanOrEqualToTen
  {
    assume {:axiom} IsValid_StringLessThanOrEqualToTen(value);
    var myStringLessThanOrEqualToTen: StringLessThanOrEqualToTen := value;
    myStringLessThanOrEqualToTen
  }

  function method ForceMyBlob(value : seq<uint8>) : MyBlob
  {
    assume {:axiom} IsValid_MyBlob(value);
    var myMyBlob: MyBlob := value;
    myMyBlob
  }

  function method ForceNonEmptyBlob(value : seq<uint8>) : NonEmptyBlob
  {
    assume {:axiom} IsValid_NonEmptyBlob(value);
    var myNonEmptyBlob: NonEmptyBlob := value;
    myNonEmptyBlob
  }

  function method ForceBlobLessThanOrEqualToTen(value : seq<uint8>) : BlobLessThanOrEqualToTen
  {
    assume {:axiom} IsValid_BlobLessThanOrEqualToTen(value);
    var myBlobLessThanOrEqualToTen: BlobLessThanOrEqualToTen := value;
    myBlobLessThanOrEqualToTen
  }

  function method ForceMyList(value : seq<string> ) : MyList
  {
    assume {:axiom} IsValid_MyList(value);
    var myMyList: MyList := value;
    myMyList
  }

  function method ForceNonEmptyList(value : seq<string> ) : NonEmptyList
  {
    assume {:axiom} IsValid_NonEmptyList(value);
    var myNonEmptyList: NonEmptyList := value;
    myNonEmptyList
  }

  function method ForceListLessThanOrEqualToTen(value : seq<string> ) : ListLessThanOrEqualToTen
  {
    assume {:axiom} IsValid_ListLessThanOrEqualToTen(value);
    var myListLessThanOrEqualToTen: ListLessThanOrEqualToTen := value;
    myListLessThanOrEqualToTen
  }

  function method ForceMyMap(value : map<string, string>) : MyMap
  {
    assume {:axiom} IsValid_MyMap(value);
    var myMyMap: MyMap := value;
    myMyMap
  }

  function method ForceNonEmptyMap(value : map<string, string>) : NonEmptyMap
  {
    assume {:axiom} IsValid_NonEmptyMap(value);
    var myNonEmptyMap: NonEmptyMap := value;
    myNonEmptyMap
  }

  function method ForceMapLessThanOrEqualToTen(value : map<string, string>) : MapLessThanOrEqualToTen
  {
    assume {:axiom} IsValid_MapLessThanOrEqualToTen(value);
    var myMapLessThanOrEqualToTen: MapLessThanOrEqualToTen := value;
    myMapLessThanOrEqualToTen
  }

  function method ForceGreaterThanOne(value : int) : GreaterThanOne
  {
    assume {:axiom} ValidInt32(value);
    var v32 := value as int32;
    assume {:axiom} IsValid_GreaterThanOne(v32);
    var myGreaterThanOne: GreaterThanOne := v32;
    myGreaterThanOne
  }
}
