// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.short

@aws.polymorph#localService(
  sdkId: "SimpleShort",
  config: SimpleShortConfig,
)
service SimpleTypesShort {
  version: "2021-11-01",
  resources: [],
  operations: [ GetShort ],
  errors: [],
}

structure SimpleShortConfig {}

operation GetShort {
  input: GetShortInput,
  output: GetShortOutput,
}

structure GetShortInput {
  value: Short
}

structure GetShortOutput {
  value: Short
}
