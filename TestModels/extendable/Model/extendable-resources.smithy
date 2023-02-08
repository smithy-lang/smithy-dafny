namespace simple.extendable.resources

@aws.polymorph#localService(
  sdkId: "SimpleExtendableResources",
  config: SimpleExtendableResourcesConfig,
)
service SimpleExtendableResources {
  version: "2021-11-01",
  resources: [ ExtendableResource ],
  operations: [ UseExtendableResources ],
  errors: [],
}

structure SimpleExtendableResourcesConfig {}

// This operation MUST
// take a native implemented resource
// and input for that resource,
// pass the input to the native resource,
// and return the native resource's output.
operation UseExtendableResources {
  input: UseExtendableResourcesInput,
  output: UseExtendableResourcesOutput,
}

structure UseExtendableResourcesInput {
  @required
  value: ExtendableResourceReference,
  @required
  input: GetResourceDataInput,
}

structure UseExtendableResourcesOutput {
  @required
  output: GetResourceDataOutput
}

@aws.polymorph#reference(resource: ExtendableResource)
structure ExtendableResourceReference {}

@aws.polymorph#extendable
resource ExtendableResource {
  operations: [
    GetResourceData,
    AlwaysModeledError,
    AlwaysMultipleErrors,
    AlwaysOpaqueError,
  ],
  errors: [ SimpleExtendableResourcesException ],
}

operation GetResourceData {
  input: GetResourceDataInput,
  output: GetResourceDataOutput,
}

structure GetResourceDataInput {
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

structure GetResourceDataOutput {
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
