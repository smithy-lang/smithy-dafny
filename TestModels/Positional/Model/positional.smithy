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
  operations: [ GetResource, GetResourcePositional ],
  errors: [],
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
  input: GetResourceInput
  output: GetResourcePositionalOutput,
}

@positional
structure GetResourcePositionalOutput {
  @required
  output: SimpleResourceReference
}
