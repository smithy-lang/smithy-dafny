namespace simple.extern

@aws.polymorph#localService(
  sdkId: "SimpleExtern",
  config: SimpleExternConfig,
)
service SimpleExtern {
  version: "2021-11-01",
  resources: [],
  operations: [ GetExtern ],
  errors: [],
}

structure SimpleExternConfig {}

// This operation eventualy calls an extern
// This is to test writing/passing externs
// in every runtime.
operation GetExtern {
  input: GetExternInput,
  output: GetExternOutput,
}

structure GetExternInput {
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

structure GetExternOutput {
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

// This operation MUST use
// an extern class that can fail
// durring construction.
// This is complicated because
// Dafny constructors MUST NOT fail.
operation UseClassExtern {
  input: UseClassExternInput,
  output: UseClassExternOutput,
}

structure UseClassExternInput {
  value: String,
}

structure UseClassExternOutput {
  value: String,
}

// This extern MUST error.
// This is to ensure that
// externs can fail.
operation ExternMustError {
  input: ExternMustErrorInput,
  output: ExternMustErrorOutput,
}

structure ExternMustErrorInput{
  value: String,
}
structure ExternMustErrorOutput{
  value: String,
}