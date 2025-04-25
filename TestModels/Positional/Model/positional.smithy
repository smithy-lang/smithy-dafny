// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.positional
use aws.polymorph#positional
use aws.polymorph#reference

@aws.polymorph#localService(
  sdkId: "SimplePositional",
  config: SimplePositionalConfig,
)
service SimplePositional {
  version: "2021-11-01",
  resources: [],
  operations: [ GetResource, GetResourcePositional, GetIntegerInputPosition, GetIntegerOutputPosition ],
  errors: [ SimplePositionalException ],
}

@error("client")
structure SimplePositionalException {
  @required
  message: String,
}

structure SimplePositionalConfig {}

resource SimpleResource {
  operations: [GetName]
}

@reference(resource: SimpleResource)
structure SimpleResourceReference {}

operation GetName {
  input: GetNameInput
  output: GetNameOutput
}

structure GetNameInput {}

structure GetNameOutput {
  @required
  name: String
}

operation GetResource {
  input: GetResourceInput
  output: GetResourceOutput,
}

structure GetResourceInput {
  @required
  name: String
}

structure GetResourceOutput {
  @required
  output: SimpleResourceReference
}

operation GetResourcePositional {
  input: GetResourcePositionalInput
  output: GetResourcePositionalOutput,
}

@positional
structure GetResourcePositionalInput {
  @required
  name: String
}

@positional
structure GetResourcePositionalOutput {
  @required
  output: SimpleResourceReference
}

operation GetIntegerInputPosition {
  input: GetIntegerInputPositionInput
  output: GetIntegerInputPositionOutput,
}

@positional
structure GetIntegerInputPositionInput {
  @required
  value: Integer
}

structure GetIntegerInputPositionOutput {
  value: Integer
}

operation GetIntegerOutputPosition {
  input: GetIntegerOutputPositionInput
  output: GetIntegerOutputPositionOutput,
}

structure GetIntegerOutputPositionInput {
  value: Integer
}

@positional
structure GetIntegerOutputPositionOutput {
  @required
  value: Integer
}