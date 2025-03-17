$version: "1.0"

// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.constraints

@aws.polymorph#localService(
  sdkId: "SimpleConstraints",
  config: SimpleConstraintsConfig,
)
service SimpleConstraints {
  version: "2021-11-01",
  resources: [],
  operations: [ GetConstraints ],
  errors: [ SimpleConstraintsException ],
}

structure SimpleConstraintsConfig {
  @required
  RequiredString: String,
}

// This is just a sanity check on the smokeTests support.
// We need to actually convert all the tests in test/WrappedSimpleConstraintsImplTest.dfy
// to smoke tests once https://github.com/smithy-lang/smithy-dafny/issues/278
// is fixed.
@smithy.test#smokeTests([
  {
    id: "GetConstraintsSuccess"
    vendorParams: {
      RequiredString: "foobar",
    }
    params: {
      OneToTen: 5,
      GreaterThanOne: 2,
      MyBlob: "0101",
      MyList: ["1", "2", "3"],
      MyMap: {
        "a": "b",
        "c": "d"
      }
    }
    expect: {
        success: {}
    }
  },
  {
    id: "GetConstraintsFailure"
    vendorParams: {
      RequiredString: "foobar",
    }
    params: {
      // These two always have to be present because of https://github.com/smithy-lang/smithy-dafny/issues/278,
      // because otherwise they are interpreted as 0.
      OneToTen: 5,
      GreaterThanOne: 2,
      // This is the member that's actually invalid
      NonEmptyBlob: ""
    }
    expect: {
        failure: {}
    }
  },
  {
    id: "GetConstraintsInvalidConfig"
    params: {}
    expect: {
      failure: {}
    },
    tags: ["INVALID_CONFIG"]
  }
])
operation GetConstraints {
  input: GetConstraintsInput,
  output: GetConstraintsOutput,
}

// See https://smithy.io/2.0/spec/constraint-traits.html

// These constraints will result
// a predicate that will define
// validity for a sub set type.
// The predicate can be tested.

@length(min: 1, max: 10)
string MyString

@length(min: 1)
string NonEmptyString

@length(max: 10)
string StringLessThanOrEqualToTen

@length(min: 1, max: 10)
blob MyBlob

@length(min: 1)
blob NonEmptyBlob

@length(max: 10)
blob BlobLessThanOrEqualToTen

@length(min: 1, max: 10)
list MyList {
  member: String
}

@length(min: 1)
list NonEmptyList {
  member: String
}

@length(max: 10)
list ListLessThanOrEqualToTen {
  member: String
}

@length(min: 1, max: 10)
list ListWithConstraint {
  member: MyString
}

@length(min: 1, max: 10)
map MyMap {
  key: String,
  value: String,
}

@length(min: 1)
map NonEmptyMap {
  key: String,
  value: String,
}

@length(max: 10)
map MapLessThanOrEqualToTen {
  key: String,
  value: String,
}

@length(min: 1, max: 10)
map MapWithConstraint {
  key: MyString,
  value: MyString,
}

// we don't do patterns yet
// @pattern("^[A-Za-z]+$")
// string Alphabetic

@range(min: 1, max: 10)
integer OneToTen

@range(min: -10, max: 10)
long TenToTen

@range(min: 1)
integer GreaterThanOne

@range(max: 10)
integer LessThanTen

// we don't do uniqueItems yet
// @uniqueItems
// list MyUniqueList {
//   member: String
// }

// @uniqueItems
// list MyComplexUniqueList {
//   member: ComplexListElement
// }

union UnionWithConstraint {
  IntegerValue: OneToTen,
  StringValue: MyString,
}

structure ComplexStructure {
  InnerString: MyString,
  @required
  InnerBlob: MyBlob,
}

@length(min: 1)
list ComplexStructureList {
  member: ComplexStructure,
}

structure GetConstraintsInput {
  MyString: MyString,
  NonEmptyString: NonEmptyString,
  StringLessThanOrEqualToTen: StringLessThanOrEqualToTen,
  MyBlob: MyBlob,
  NonEmptyBlob: NonEmptyBlob,
  BlobLessThanOrEqualToTen: BlobLessThanOrEqualToTen,
  MyList: MyList,
  NonEmptyList: NonEmptyList,
  ListLessThanOrEqualToTen: ListLessThanOrEqualToTen,
  ListWithConstraint: ListWithConstraint,
  MyMap: MyMap,
  NonEmptyMap: NonEmptyMap,
  MapLessThanOrEqualToTen: MapLessThanOrEqualToTen,
  MapWithConstraint: MapWithConstraint,
  // Alphabetic: Alphabetic,
  OneToTen: OneToTen,
  myTenToTen: TenToTen,
  GreaterThanOne: GreaterThanOne,
  LessThanTen: LessThanTen,
  // MyUniqueList: MyUniqueList,
  // MyComplexUniqueList: MyComplexUniqueList,
  MyUtf8Bytes: Utf8Bytes,
  MyListOfUtf8Bytes: ListOfUtf8Bytes,
  UnionWithConstraint: UnionWithConstraint,
  ComplexStructureList: ComplexStructureList,
}

structure GetConstraintsOutput {
  MyString: MyString,
  NonEmptyString: NonEmptyString,
  StringLessThanOrEqualToTen: StringLessThanOrEqualToTen,
  MyBlob: MyBlob,
  NonEmptyBlob: NonEmptyBlob,
  BlobLessThanOrEqualToTen: BlobLessThanOrEqualToTen,
  MyList: MyList,
  NonEmptyList: NonEmptyList,
  ListLessThanOrEqualToTen: ListLessThanOrEqualToTen,
  ListWithConstraint: ListWithConstraint,
  MyMap: MyMap,
  NonEmptyMap: NonEmptyMap,
  MapLessThanOrEqualToTen: MapLessThanOrEqualToTen,
  MapWithConstraint: MapWithConstraint,
  // Alphabetic: Alphabetic,
  OneToTen: OneToTen,
  thatTenToTen: TenToTen,
  GreaterThanOne: GreaterThanOne,
  LessThanTen: LessThanTen,
  // MyUniqueList: MyUniqueList,
  // MyComplexUniqueList: MyComplexUniqueList,
  MyUtf8Bytes: Utf8Bytes,
  MyListOfUtf8Bytes: ListOfUtf8Bytes,
  UnionWithConstraint: UnionWithConstraint,
  ComplexStructureList: ComplexStructureList,
}

// See Comment in traits.smithy
@aws.polymorph#dafnyUtf8Bytes
@length(min: 1, max: 10)
string Utf8Bytes

@length(min: 1, max: 2)
list ListOfUtf8Bytes {
  member: Utf8Bytes
}

@error("client")
structure SimpleConstraintsException {
  @required
  message: String,
}
