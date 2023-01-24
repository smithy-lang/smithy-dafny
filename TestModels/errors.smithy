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
    AlwaysMultipuleErrors,
    AlwaysNativeError,
  ],
  errors: [],
}

structure SimpleErrorsConfig {}

// This operation MUST ==> SimpleErrorsException
operation AlwaysError {
  input: GetErrorsInput,
  output: GetErrorsOutput,
}

// This operation MUST ==> an list of errors
operation AlwaysMultipuleErrors {
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


// this SHOULD also alow no message,
// and other/multipule values
@error("client")
structure SimpleErrorsException {
  @required
  message: String,
}
