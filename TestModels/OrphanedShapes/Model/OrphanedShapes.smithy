// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

$version: "2"
namespace simple.orphaned

@aws.polymorph#localService(
  sdkId: "SimpleOrphaned",
  config: SimpleOrphanedConfig,
)
service SimpleOrphaned {
  version: "2021-11-01",
  resources: [],
  operations: [],
}

structure SimpleOrphanedConfig {
  structureMember: OrphanedConfigShape
}

structure OrphanedConfigShape {
  stringMember: String
}

blob OrphanedBlob

boolean OrphanedBoolean

string OrphanedString

// TODO: Once SimpleTypes for commented-out shapes are completed,
// uncomment these and add as members to OrphanedStructure
// byte OrphanedByte

// short OrphanedShort

integer OrphanedInteger

long OrphanedLong

// float OrphanedFloat

// double OrphanedDouble

// bigInteger OrphanedBigInteger

// bigDecimal OrphanedBigDecimal

// timestamp OrphanedTimestamp

// document OrphanedDocument

// This is a smithy V1 Enum
@enum([
  {
    name: "FIRST",
    value: "0x0014",
  },
  {
    name: "SECOND",
    value: "0x0046",
  },
  {
    name: "THIRD",
    value: "0x0078",
  },
])
string OrphanedV1Enum

list OrphanedList {
  member: String
}

map OrphanedMap {
  key: String
  value: String
}

structure OrphanedStructure {
    blobValue: OrphanedBlob,
    booleanValue: OrphanedBoolean,
    stringValue: OrphanedString,
    //  byteValue: OrphanedByte,
    //  shortValue: OrphanedShort,
    integerValue: OrphanedInteger,
    longValue: OrphanedLong,
    //  floatValue: OrphanedFloat,
    //  doubleValue: OrphanedDouble,
    //  bigIntegerValue: OrphanedBigInteger,
    //  bigDecimalValue: OrphanedBigDecimal,
    //  timestampValue: OrphanedTimestamp,
    unionValue: OrphanedUnion,
    enumValue: OrphanedV1Enum,
    mapValue: OrphanedMap,
    listValue: OrphanedList
}

union OrphanedUnion {
  integerValue: Integer
  stringValue: String
}

@error("client")
structure OrphanedError {
  @required
  message: String,
}

@aws.polymorph#reference(resource: OrphanedResource)
structure OrphanedResourceReference {}

@aws.polymorph#extendable
resource OrphanedResource {
  operations: [
    OrphanedResourceOperation
  ]
}

operation OrphanedResourceOperation {
    input: OrphanedResourceOperationInput
    output: OrphanedResourceOperationOutput
}

structure OrphanedResourceOperationInput {
  someString: String
}

structure OrphanedResourceOperationOutput {
  someString: String
}
