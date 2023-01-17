namespace simple.refinement

@aws.polymorph#localService(
  sdkId: "SimpleRefinement",
  config: SimpleRefinementConfig,
)
service SimpleRefinement {
  version: "2021-11-01",
  resources: [],
  operations: [ GetRefinement ],
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
  requiredString: string,
  optionalString: string,
}

@output
structure GetRefinementOutput {
  @required
  requiredString: string,
  optionalString: string,
}

operation OnlyInput {
  input: OnlyInputInput,
}

@input
structure OnlyInputInput {
  value: string,
}

operation OnlyOutput {
  output: OnlyOutputOutput,
}

@output
structure OnlyOutputOutput {
  value: string,
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
  requiredString: string,
  optionalString: string,
}
structure ReadonlyOperationOutput {
  @required
  requiredString: string,
  optionalString: string,
}

