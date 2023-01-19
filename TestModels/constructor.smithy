namespace simple.constructor

@aws.polymorph#localService(
  sdkId: "SimpleConstructor",
  config: SimpleConstructorConfig,
)
service SimpleConstructor {
  version: "2021-11-01",
  resources: [],
  operations: [ GetConstructor ],
  errors: [],
}

structure SimpleConstructorConfig {
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

// This operation MUST
// return the values given in the constructor.
// The internal config MUST somehow differ,
// and this additional information MUST be returned.
operation GetConstructor {
  input: GetConstructorInput,
  output: GetConstructorOutput,
}

structure GetConstructorInput {
  value: String
}

structure GetConstructorOutput {
  internalConfigString: string,
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
