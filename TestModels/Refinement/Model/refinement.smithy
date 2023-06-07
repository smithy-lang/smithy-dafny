// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.refinement

@aws.polymorph#localService(
  sdkId: "SimpleRefinement",
  config: SimpleRefinementConfig,
)
service SimpleRefinement {
  version: "2021-11-01",
  resources: [],
  operations: [ GetRefinement, OnlyInput, OnlyOutput, ReadonlyOperation ],
  errors: [],
}

structure SimpleRefinementConfig {}

operation GetRefinement {
  input: GetRefinementInput,
  output: GetRefinementOutput,
}

@input
structure GetRefinementInput {
  @required
  requiredString: String,
  optionalString: String,
}

@output
structure GetRefinementOutput {
  @required
  requiredString: String,
  optionalString: String,
}

operation OnlyInput {
  input: OnlyInputInput,
}

@input
structure OnlyInputInput {
  value: String,
}

operation OnlyOutput {
  output: OnlyOutputOutput,
}

@output
structure OnlyOutputOutput {
  value: String,
}

// Dafny treats @readonly as a function.
// This is because Smithy treats
// All operations that are marked as readonly trait are inherently idempotent.
@readonly
operation ReadonlyOperation {
  input: ReadonlyOperationInput,
  output: ReadonlyOperationOutput,
}

structure ReadonlyOperationInput {
  @required
  requiredString: String,
  optionalString: String,
}
structure ReadonlyOperationOutput {
  @required
  requiredString: String,
  optionalString: String,
}