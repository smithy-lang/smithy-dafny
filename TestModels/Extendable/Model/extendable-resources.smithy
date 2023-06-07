// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.extendable.resources

@aws.polymorph#localService(
  sdkId: "SimpleExtendableResources",
  config: SimpleExtendableResourcesConfig,
)
service SimpleExtendableResources {
  version: "2021-11-01",
  resources: [ ExtendableResource ],
  operations: [
    CreateExtendableResource,
    UseExtendableResource,
    UseExtendableResourceAlwaysModeledError,
    UseExtendableResourceAlwaysMultipleErrors,
    UseExtendableResourceAlwaysOpaqueError
  ],
  errors: [],
}

structure SimpleExtendableResourcesConfig {}

@aws.polymorph#reference(resource: ExtendableResource)
structure ExtendableResourceReference {}

operation CreateExtendableResource {
  input: CreateExtendableResourceInput ,
  output: CreateExtendableResourceOutput
}

@length(min: 1) string Name

structure CreateExtendableResourceInput {
  @required name: Name
}

structure CreateExtendableResourceOutput {
  @required resource: ExtendableResourceReference
}

// This operation MUST
// take a native implemented resource
// and input for that resource,
// pass the input to the native resource,
// and return the native resource's output.
operation UseExtendableResource {
  input: UseExtendableResourceInput,
  output: UseExtendableResourceOutput,
}

structure UseExtendableResourceInput {
  @required resource: ExtendableResourceReference,
  @required input: GetExtendableResourceDataInput,
}

structure UseExtendableResourceOutput {
  @required output: GetExtendableResourceDataOutput
}

operation UseExtendableResourceAlwaysModeledError {
  input: UseExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

structure UseExtendableResourceErrorsInput {
  @required resource: ExtendableResourceReference,
  @required input: GetExtendableResourceErrorsInput,
}

operation UseExtendableResourceAlwaysMultipleErrors {
  input: UseExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

operation UseExtendableResourceAlwaysOpaqueError {
  input: UseExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

@aws.polymorph#extendable
resource ExtendableResource {
  operations: [
    GetExtendableResourceData,
    AlwaysModeledError,
    AlwaysMultipleErrors,
    AlwaysOpaqueError,
  ],
  errors: [ SimpleExtendableResourcesException ],
}

operation GetExtendableResourceData {
  input: GetExtendableResourceDataInput,
  output: GetExtendableResourceDataOutput,
}

structure GetExtendableResourceDataInput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  //  byteValue: Byte,
  //  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
  //  floatValue: Float,
  //  doubleValue: Double,
  //  bigIntegerValue: BigInteger,
  //  bigDecimalValue: BigDecimal,
  //  timestampValue: Timestamp,
}

structure GetExtendableResourceDataOutput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  //  byteValue: Byte,
  //  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
  //  floatValue: Float,
  //  doubleValue: Double,
  //  bigIntegerValue: BigInteger,
  //  bigDecimalValue: BigDecimal,
  //  timestampValue: Timestamp,
}

// This operation MUST ==> SimpleExtendableResourcesException
operation AlwaysModeledError {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

// This operation MUST ==> an list of errors
operation AlwaysMultipleErrors {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

// This operation MUST ==> native unmodled error
operation AlwaysOpaqueError {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

structure GetExtendableResourceErrorsInput {
  value: String,
}

structure GetExtendableResourceErrorsOutput {
  value: String,
}

@error("client")
structure SimpleExtendableResourcesException {
  @required
  message: String,
}
