// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleConstraintsImpl.dfy"
include "SimpleConstraintsImplTest.dfy"

module WrappedSimpleConstraintsTest {
  import opened WrappedSimpleConstraintsService
  import opened SimpleConstraintsTypes
  import opened Helpers
  import SimpleConstraintsImplTest
  import opened Wrappers
  import opened StandardLibrary.UInt
  method{:test} TestConstraints() {
    var client :- expect WrappedSimpleConstraintsService.WrappedSimpleConstraints();
    TestGetConstraintWithValidInputs(client);
    TestGetConstraintWithMyString(client);
    TestGetConstraintWithOneToTen(client);
    TestGetConstraintWithTenToTen(client);
    TestGetConstraintWithLessThanTen(client);
    TestGetConstraintWithNonEmptyString(client);
    TestGetConstraintWithStringLessThanOrEqualToTen(client);
    TestGetConstraintWithMyBlob(client);
    TestGetConstraintWithNonEmptyBlob(client);
    TestGetConstraintWithBlobLessThanOrEqualToTen(client);
    TestGetConstraintWithMyList(client);
    TestGetConstraintWithNonEmptyList(client);
    TestGetConstraintWithListLessThanOrEqualToTen(client);
    TestGetConstraintWithListWithConstraint(client);
    TestGetConstraintWithMyMap(client);
    TestGetConstraintWithNonEmptyMap(client);
    TestGetConstraintWithMapLessThanOrEqualToTen(client);
    TestGetConstraintWithMapWithConstraint(client);
    TestGetConstraintWithGreaterThanOne(client);
    TestGetConstraintWithUtf8Bytes(client);
    TestGetConstraintWithListOfUtf8Bytes(client);
    TestGetConstraintWithComplexStructureList(client);

    var allowBadUtf8BytesFromDafny := true;
    if (allowBadUtf8BytesFromDafny) {
      TestGetConstraintWithBadUtf8Bytes(client);
      TestGetConstraintWithListOfBadUtf8Bytes(client);
    }

    // This doesn't work in Java.
    // See https://github.com/smithy-lang/smithy-dafny/issues/278
    var supportsOptionalPrimitiveFields := true;
    if (supportsOptionalPrimitiveFields) {
      TestGetConstraintWithUnionWithConstraint(client);
    }
  }

  method TestGetConstraintWithValidInputs(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithMyString(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MyString := Some(ForceMyString("this string is really way too long")));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyString := Some(ForceMyString("12345678901")));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyString := Some(ForceMyString("1234567890")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyString := Some(ForceMyString("1")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyString := Some(ForceMyString("")));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @range(min: 1, max: 10)
  method TestGetConstraintWithOneToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(OneToTen := Some(ForceOneToTen(1000)));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(OneToTen := Some(ForceOneToTen(-1000)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(OneToTen := Some(ForceOneToTen(0)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(OneToTen := Some(ForceOneToTen(1)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(OneToTen := Some(ForceOneToTen(10)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(OneToTen := Some(ForceOneToTen(11)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @range(min: -10, max: 10) -- type long
  method TestGetConstraintWithTenToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(myTenToTen := Some(ForceTenToTen(1000)));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(myTenToTen := Some(ForceTenToTen(-1000)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(myTenToTen := Some(ForceTenToTen(-11)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(myTenToTen := Some(ForceTenToTen(-10)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(myTenToTen := Some(ForceTenToTen(0)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(myTenToTen := Some(ForceTenToTen(10)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(myTenToTen := Some(ForceTenToTen(11)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @range(max: 10)
  method TestGetConstraintWithLessThanTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(LessThanTen := Some(ForceLessThanTen(1000)));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(LessThanTen := Some(ForceLessThanTen(-1000)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(LessThanTen := Some(ForceLessThanTen(0)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(LessThanTen := Some(ForceLessThanTen(1)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(LessThanTen := Some(ForceLessThanTen(10)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(LessThanTen := Some(ForceLessThanTen(11)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1)
  method TestGetConstraintWithNonEmptyString(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(NonEmptyString := Some(ForceNonEmptyString("this string is really way too long")));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyString := Some(ForceNonEmptyString("12345678901")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyString := Some(ForceNonEmptyString("1234567890")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyString := Some(ForceNonEmptyString("1")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyString := Some(ForceNonEmptyString("")));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(max: 10)
  method TestGetConstraintWithStringLessThanOrEqualToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(StringLessThanOrEqualToTen := Some(ForceStringLessThanOrEqualToTen("this string is really way too long")));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(StringLessThanOrEqualToTen := Some(ForceStringLessThanOrEqualToTen("12345678901")));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(StringLessThanOrEqualToTen := Some(ForceStringLessThanOrEqualToTen("1234567890")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(StringLessThanOrEqualToTen := Some(ForceStringLessThanOrEqualToTen("1")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(StringLessThanOrEqualToTen := Some(ForceStringLessThanOrEqualToTen("")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithMyBlob(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MyBlob := Some(ForceMyBlob([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyBlob := Some(ForceMyBlob([1])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyBlob := Some(ForceMyBlob([1,2,3,4,5,6,7,8,9,0])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyBlob := Some(ForceMyBlob([1,2,3,4,5,6,7,8,9,0,1])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1)
  method TestGetConstraintWithNonEmptyBlob(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(NonEmptyBlob := Some(ForceNonEmptyBlob([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(NonEmptyBlob := Some(ForceNonEmptyBlob([1])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyBlob := Some(ForceNonEmptyBlob([1,2,3,4,5,6,7,8,9,0])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(max: 10)
  method TestGetConstraintWithBlobLessThanOrEqualToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(BlobLessThanOrEqualToTen := Some(ForceBlobLessThanOrEqualToTen([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(BlobLessThanOrEqualToTen := Some(ForceBlobLessThanOrEqualToTen([1])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(BlobLessThanOrEqualToTen := Some(ForceBlobLessThanOrEqualToTen([1,2,3,4,5,6,7,8,9,0])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(BlobLessThanOrEqualToTen := Some(ForceBlobLessThanOrEqualToTen([1,2,3,4,5,6,7,8,9,0,1])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithMyList(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MyList := Some(ForceMyList([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyList := Some(ForceMyList(["1"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyList := Some(ForceMyList(["1","2","3","4","5","6","7","8","9","0"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyList := Some(ForceMyList(["1","2","3","4","5","6","7","8","9","0","a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1)
  method TestGetConstraintWithNonEmptyList(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(NonEmptyList := Some(ForceNonEmptyList([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(NonEmptyList := Some(ForceNonEmptyList(["1"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyList := Some(ForceNonEmptyList(["1","2","3","4","5","6","7","8","9","0"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyList := Some(ForceNonEmptyList(["1","2","3","4","5","6","7","8","9","0","a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(max: 10)
  method TestGetConstraintWithListLessThanOrEqualToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(ListLessThanOrEqualToTen := Some(ForceListLessThanOrEqualToTen([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(ListLessThanOrEqualToTen := Some(ForceListLessThanOrEqualToTen(["1"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(ListLessThanOrEqualToTen := Some(ForceListLessThanOrEqualToTen(["1","2","3","4","5","6","7","8","9","0"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(ListLessThanOrEqualToTen := Some(ForceListLessThanOrEqualToTen(["1","2","3","4","5","6","7","8","9","0","a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // both list and member have @length(min: 1, max: 10)
  method TestGetConstraintWithListWithConstraint(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(ListWithConstraint := Some(["1", "2", "3"]));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    // TODO: Add negative tests once all languages support it
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithMyMap(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MyMap := Some(ForceMyMap(map[])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyMap := Some(ForceMyMap(map["1" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyMap := Some(ForceMyMap(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyMap := Some(ForceMyMap(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a", "a" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1)
  method TestGetConstraintWithNonEmptyMap(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(NonEmptyMap := Some(ForceNonEmptyMap(map[])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(NonEmptyMap := Some(ForceNonEmptyMap(map["1" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyMap := Some(ForceNonEmptyMap(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(NonEmptyMap := Some(ForceNonEmptyMap(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a", "a" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(max: 10)
  method TestGetConstraintWithMapLessThanOrEqualToTen(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MapLessThanOrEqualToTen := Some(ForceMapLessThanOrEqualToTen(map[])));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MapLessThanOrEqualToTen := Some(ForceMapLessThanOrEqualToTen(map["1" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MapLessThanOrEqualToTen := Some(ForceMapLessThanOrEqualToTen(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MapLessThanOrEqualToTen := Some(ForceMapLessThanOrEqualToTen(map["1" := "a", "2" := "a", "3" := "a", "4" := "a", "5" := "a", "6" := "a", "7" := "a", "8" := "a", "9" := "a", "0" := "a", "a" := "a"])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // both map and member have @length(min: 1, max: 10)
  method TestGetConstraintWithMapWithConstraint(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MapWithConstraint := Some(map["0" := "1234", "abcd" := "j"]));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    // TODO: Add negative tests once all languages support it
  }

  // @range(min: 1)
  method TestGetConstraintWithGreaterThanOne(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(GreaterThanOne := Some(ForceGreaterThanOne(1000)));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(GreaterThanOne := Some(ForceGreaterThanOne(-1000)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(GreaterThanOne := Some(ForceGreaterThanOne(0)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(GreaterThanOne := Some(ForceGreaterThanOne(1)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithUtf8Bytes(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes([1])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes([1,2,3,4,5,6,7,8,9,0])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes([1,2,3,4,5,6,7,8,9,0,1])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    var one : seq<uint8> := [0xf0, 0xa8, 0x89, 0x9f];
    var two : seq<uint8> := [0xc2, 0xa3];
    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(one)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(one + one)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    // 3 characters, but exceeds 10 bytes
    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(one + one + one)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(two + two + two + two + two + two + two + two + two + two)));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(two + two + two + two + two + two + two + two + two + two + two)));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    // Current implementation counts utf16 code units
    // however, generated Dafny count utf8-bytes,
    // Plan is to simply reject anything but (min:1)
    //
    // input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(one + one + one + one + one + one + one + one + one + one)));
    // ret := client.GetConstraints(input := input);
    // expect ret.Success?;

    // input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes(one + one + one + one + one + one + one + one + one + one + one)));
    // ret := client.GetConstraints(input := input);
    // expect ret.Failure?;
  }

  // @length(min: 1, max: 10)
  method TestGetConstraintWithBadUtf8Bytes(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    // good length, bad bytes
    var input := GetValidInput();
    input := input.(MyUtf8Bytes := Some(ForceUtf8Bytes([255,255,255])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1, max: 2)
  method TestGetConstraintWithListOfUtf8Bytes(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var good := ForceUtf8Bytes([1,2,3]);

    var input := GetValidInput();
    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([good])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([good, good])));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([good, good, good])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  // @length(min: 1, max: 2)
  method TestGetConstraintWithListOfBadUtf8Bytes(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var bad := ForceUtf8Bytes([255,255,255]);
    var good := ForceUtf8Bytes([1,2,3]);

    var input := GetValidInput();
    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([bad])));
    var ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([bad, good])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;

    input := input.(MyListOfUtf8Bytes := Some(ForceListOfUtf8Bytes([good, bad])));
    ret := client.GetConstraints(input := input);
    expect ret.Failure?;
  }

  method TestGetConstraintWithUnionWithConstraint(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(UnionWithConstraint := Some(IntegerValue(1)));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    input := GetValidInput();
    input := input.(UnionWithConstraint := Some(StringValue("foo")));
    ret := client.GetConstraints(input := input);
    expect ret.Success?;

    // TODO: Add negative tests once all languages support it
  }

  method TestGetConstraintWithComplexStructureList(client: ISimpleConstraintsClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var input := GetValidInput();
    input := input.(ComplexStructureList := Some([
      ComplexStructure(InnerString := Some("a"), InnerBlob := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
      ComplexStructure(InnerString := Some("abcdefghij"), InnerBlob := [0])
    ]));
    var ret := client.GetConstraints(input := input);
    expect ret.Success?;

    // TODO: Add negative tests once all languages support it
  }
}
