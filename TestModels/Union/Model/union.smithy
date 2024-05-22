// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.union

@aws.polymorph#localService(
  sdkId: "SimpleUnion",
  config: SimpleUnionConfig,
)
service SimpleUnion {
  version: "2021-11-01",
  operations: [ GetUnion, GetKnownValueUnion ]
}

structure SimpleUnionConfig {}

operation GetUnion {
  input: GetUnionInput,
  output: GetUnionOutput
}

structure GetUnionInput {
    union: MyUnion
}

structure GetUnionOutput {
    union: MyUnion
}

union MyUnion {
    IntegerValue: Integer,
    StringValue: String
}

operation GetKnownValueUnion {
  input: GetKnownValueUnionInput,
  output: GetKnownValueUnionOutput
}

structure GetKnownValueUnionInput {
    union: KnownValueUnion
}

structure GetKnownValueUnionOutput {
    union: KnownValueUnion
}

union KnownValueUnion {
    Value: Integer
}
