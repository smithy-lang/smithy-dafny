// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

$version: "2"

namespace simple.types.enumV2

@aws.polymorph#localService(
  sdkId: "SimpleEnumV2",
  config: SimpleEnumV2Config,
)
service SimpleTypesEnumV2 {
  version: "2021-11-01",
  resources: [],
  operations: [
    GetEnumV2,
    GetEnumV2FirstKnownValueTest,
    GetEnumV2SecondKnownValueTest,
    GetEnumV2ThirdKnownValueTest,
  ],
  errors: [],
}

structure SimpleEnumV2Config {}

operation GetEnumV2 {
  input: GetEnumV2Input,
  output: GetEnumV2Output,
}

operation GetEnumV2FirstKnownValueTest {
  input: GetEnumV2Input,
  output: GetEnumV2Output,
}

operation GetEnumV2SecondKnownValueTest {
  input: GetEnumV2Input,
  output: GetEnumV2Output,
}

operation GetEnumV2ThirdKnownValueTest {
  input: GetEnumV2Input,
  output: GetEnumV2Output,
}

structure GetEnumV2Input {
  value: SimpleEnumV2Shape
}

structure GetEnumV2Output {
  value: SimpleEnumV2Shape
}

// This is a smithy V2 Enum
enum SimpleEnumV2Shape {
    FIRST = "0x0014"
    SECOND = "0x0046"
    THIRD = "0x0078"
}
