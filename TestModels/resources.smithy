namespace simple.resources

@aws.polymorph#localService(
  sdkId: "SimpleResources",
  config: SimpleResourcesConfig,
)
service SimpleResources {
  version: "2021-11-01",
  resources: [],
  operations: [ GetResources ],
  errors: [],
}

structure SimpleResourcesConfig {}

// This operation MUST
// return the values given in the Resources.
// The internal config MUST somehow differ,
// and this additional information MUST be returned.
operation GetResources {
  input: GetResourcesInput,
  output: GetResourcesOutput,
}

structure GetResourcesInput {
  value: String
}

structure GetResourcesOutput {
  @required
  output: SimpleResourceReference
}

@aws.polymorph#reference(resource: SimpleResource)
structure SimpleResourceReference {}

resource SimpleResource {
  operations: [ GetResourceData ]
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

structure SimpleResourceException {
  @required
  message: String,
}

