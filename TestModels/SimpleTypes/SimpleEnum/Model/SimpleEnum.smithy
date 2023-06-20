// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.smithyEnum

@aws.polymorph#localService(
  sdkId: "SimpleEnum",
  config: SimpleEnumConfig,
)
service SimpleTypesEnum {
  version: "2021-11-01",
  resources: [],
  operations: [ GetEnum,
                GetEnumFirstKnownValueTest, 
                GetEnumSecondKnownValueTest, 
                GetEnumThirdKnownValueTest ],
  errors: [],
}

structure SimpleEnumConfig {}

operation GetEnum {
  input: GetEnumInput,
  output: GetEnumOutput,
}

operation GetEnumFirstKnownValueTest {
  input: GetEnumInput,
  output: GetEnumOutput,
}

operation GetEnumSecondKnownValueTest {
  input: GetEnumInput,
  output: GetEnumOutput,
}

operation GetEnumThirdKnownValueTest {
  input: GetEnumInput,
  output: GetEnumOutput,
}

structure GetEnumInput {
  value: SimpleEnumShape
}

structure GetEnumOutput {
  value: SimpleEnumShape
}

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
string SimpleEnumShape
