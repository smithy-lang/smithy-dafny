// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.errors

use aws.polymorph#localService

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
  errors: [ SimpleErrorsException ],
}

structure SimpleErrorsConfig {}

// This operation MUST ==> SimpleErrorsException
operation AlwaysError {
  input: GetErrorsInput,
  output: GetErrorsOutput,
  errors: [ SimpleErrorsException ]
}

// This operation MUST ==> an list of errors
operation AlwaysMultipleErrors {
  input: GetErrorsInput,
  output: GetErrorsOutput,
}

// This operation MUST ==> native unmodeled error
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

// TODO: this SHOULD also allow no message (i.e. no `@required` trait) and other/multiple members.
// However, codegen currently does not support either of these extensions.
// We will come back and extend this exception after creating more of the testbed.
// SIM: CrypTool-5085
@error("client")
structure SimpleErrorsException {
  @required
  message: String,
}