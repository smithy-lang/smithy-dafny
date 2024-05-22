// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.integer

@aws.polymorph#localService(
  sdkId: "SimpleInteger",
  config: SimpleIntegerConfig,
)
service SimpleTypesInteger {
  version: "2021-11-01",
  resources: [],
  operations: [ GetInteger, GetIntegerKnownValueTest ],
  errors: [],
}

structure SimpleIntegerConfig {}

operation GetInteger {
  input: GetIntegerInput,
  output: GetIntegerOutput,
}

operation GetIntegerKnownValueTest {
  input: GetIntegerInput,
  output: GetIntegerOutput,
}

structure GetIntegerInput {
  value: Integer
}

structure GetIntegerOutput {
  value: Integer
}