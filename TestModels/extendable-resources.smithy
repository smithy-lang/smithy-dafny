namespace simple.extendable.resources

@aws.polymorph#localService(
  sdkId: "SimpleExtendableResources",
  config: SimpleExtendableResourcesConfig,
)
service SimpleExtendableResources {
  version: "2021-11-01",
  Extendableresources: [],
  operations: [ GetExtendableResources ],
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
    AlwaysError,
    AlwaysMultipuleErrors,
    AlwaysNativeError,
  ],
}

operation GetResourceData {
  input: GetResourceDataInput,
  output: GetResourceDataOutput,
}

structure GetResourceDataInput {
  blobValue: blob,
  booleanValue: boolean,
  stringValue: string,
  byteValue: byte,
  shortValue: short,
  integerValue: integer,
  longValue: long,
  floatValue: float,
  doubleValue: double,
  bigIntegerValue: bigInteger,
  bigDecimalValue: bigDecimal,
  timestampValue: timestamp,
}

structure GetResourceDataOutput {
  blobValue: blob,
  booleanValue: boolean,
  stringValue: string,
  byteValue: byte,
  shortValue: short,
  integerValue: integer,
  longValue: long,
  floatValue: float,
  doubleValue: double,
  bigIntegerValue: bigInteger,
  bigDecimalValue: bigDecimal,
  timestampValue: timestamp,
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
  value: string,
}

structure GetExtendableResourceErrorsOutput {
  value: string,
}

// this SHOULD also alow no message,
// and other/multipule values
@error("client")
structure SimpleResourceException {
  @required
  message: String,
}
