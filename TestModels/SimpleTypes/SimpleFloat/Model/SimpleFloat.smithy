// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.float

@aws.polymorph#localService(
  sdkId: "SimpleFloat",
  config: SimpleFloatConfig,
)
service SimpleTypesFloat {
  version: "2021-11-01",
  resources: [],
  operations: [ GetFloat ],
  errors: [],
}

structure SimpleFloatConfig {}

operation GetFloat {
  input: GetFloatInput,
  output: GetFloatOutput,
}

structure GetFloatInput {
  value: Float
}

structure GetFloatOutput {
  value: Float
}