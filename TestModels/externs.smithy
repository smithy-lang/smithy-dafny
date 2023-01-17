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

structure GetExternOutput {
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
  value: string,
}

structure UseClassExternOutput {
  value: string,
}

// This extern MUST error.
// This is to ensure that
// externs can fail.
operation ExternMustError {
  input: ExternMustErrorInput,
  output: ExternMustErrorOutput,
}

structure ExternMustErrorInput{
  value: string,
}
structure ExternMustErrorOutput{
  value: string,
}