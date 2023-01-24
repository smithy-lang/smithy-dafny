namespace simple.extendable.resources

@aws.polymorph#localService(
  sdkId: "SimpleExtendableResources",
  config: SimpleExtendableResourcesConfig,
)
service SimpleExtendableResources {
  version: "2021-11-01",
  Extendableresources: [],
  operations: [ UseExtendableResources ],
  errors: [],
}

structure SimpleExtendableResourcesConfig {}

// This operation MUST
// take an native implemented resource
// and input for that resource,
// pass the input to the resource,
// and return the resources output.
operation UseExtendableResources {
  input: UseExtendableResourcesInput,
  output: UseExtendableResourcesOutput,
}

structure UseExtendableResourcesInput {
  @required
  value: ExtendableResourceReference,
  @required
  input: GetExtendableResourceDataInput,
}

structure UseExtendableResourcesOutput {
  @required
  output: GetExtendableResourceDataOutput
}

@aws.polymorph#reference(resource: ExtendableResource)
structure ExtendableResourceReference {}

@aws.polymorph#extendable
resource ExtendableResource {
  operations: [
    GetResourceData,
    AlwaysError,
    AlwaysMultipuleErrors,
    AlwaysNativeError,
  ],
}

operation GetResourceData {
  input: GetExtendableResourceDataInput,
  output: GetExtendableResourceDataOutput,
}

structure GetExtendableResourceDataInput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  byteValue: Byte,
  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
  floatValue: Float,
  doubleValue: Double,
  bigIntegerValue: BigInteger,
  bigDecimalValue: BigDecimal,
  timestampValue: Timestamp,
}

structure GetExtendableResourceDataOutput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  byteValue: Byte,
  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
  floatValue: Float,
  doubleValue: Double,
  bigIntegerValue: BigInteger,
  bigDecimalValue: BigDecimal,
  timestampValue: Timestamp,
}

// This operation MUST ==> SimpleResourceException
operation AlwaysError {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

// This operation MUST ==> an list of errors
operation AlwaysMultipuleErrors {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

// This operation MUST ==> native unmodled error
operation AlwaysNativeError {
  input: GetExtendableResourceErrorsInput,
  output: GetExtendableResourceErrorsOutput,
}

structure GetExtendableResourceErrorsInput {
  value: String,
}

structure GetExtendableResourceErrorsOutput {
  value: String,
}

// this SHOULD also alow no message,
// and other/multipule values
@error("client")
structure SimpleResourceException {
  @required
  message: String,
}
