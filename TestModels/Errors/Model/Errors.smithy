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

// This operation MUST ==> an list of errors
operation AlwaysMultipleErrors {
  input: GetErrorsInput,
  output: GetErrorsOutput,
}

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

structure AlwaysErrorInput {
  value: SimpleErrorsException,
}

structure AlwaysErrorOutput {
  value: SimpleErrorsException,
}

// this SHOULD also alow no message,
// and other/multiple values
@error("client")
structure SimpleErrorsException {
  @required
  message: String,
}