namespace simple.errors

@aws.polymorph#localService(
  sdkId: "SimpleErrors",
  config: SimpleErrorsConfig,
)
service SimpleErrors {
  version: "2021-11-01",
  resources: [],
  operations: [
    AlwaysError,
    AlwaysMultipleErrors,
    AlwaysNativeError,
  ],
  errors: [],
}

structure SimpleErrorsConfig {}

// This operation MUST ==> SimpleErrorsException
operation AlwaysError {
  input: AlwaysErrorInput,
  output: AlwaysErrorOutput,
}

structure AlwaysErrorInput {
  value: SimpleErrorsException,
}

structure AlwaysErrorOutput {
  value: SimpleErrorsException,
}

// Below this line I haven't changed in code yet, as this would require more codegen debug.
// I've thought about AlwaysMultipleErrors and outlined what I'd try in comments.
// I haven't thought through AlwaysNativeError changes yet.

// This operation MUST ==> an list of errors
operation AlwaysMultipleErrors {
  input: GetErrorsInput,
  output: GetErrorsOutput,
}

// operation AlwaysMultipleErrors {
//   input: AlwaysMultipleErrorsInput,
//   output: AlwaysMultipleErrorsOutput,
// }

// @sparse
// list AlwaysMultipleErrorsInput {
//   member: SimpleErrorsException,
// }

// @sparse
// list AlwaysMultipleErrorsOutput {
//   member: SimpleErrorsException,
// }

// This operation MUST ==> native unmodled error
operation AlwaysNativeError {
  input: GetErrorsInput,
  output: GetErrorsOutput,
}

structure GetErrorsInput {
  value: String,
}

structure GetErrorsOutput {
  value: String,
}

// this SHOULD also alow no message,
// and other/multiple values
@error("client")
structure SimpleErrorsException {
  @required // Codegen fails if I remove @requried
  message: String,

  // Codegen fails if I add more members
}