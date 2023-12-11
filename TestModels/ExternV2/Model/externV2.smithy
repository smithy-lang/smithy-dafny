// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.dafnyExternV2

@aws.polymorph#localService(
  sdkId: "SimpleExternV2",
  config: SimpleExternV2Config,
)
service SimpleExternV2 {
  version: "2021-11-01",
  resources: [],
  operations: [ GetExternV2, UseClassExternV2, ExternV2MustError ],
  errors: [],
}

structure SimpleExternV2Config {}

// This operation eventualy calls an extern
// This is to test writing/passing externs
// in every runtime.
operation GetExternV2 {
  input: GetExternV2Input,
  output: GetExternV2Output,
}

structure GetExternV2Input {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  integerValue: Integer,
  longValue: Long,
  //byteValue: byte,
  //shortValue: short,
  //floatValue: float,
  //doubleValue: double,
  //bigIntegerValue: bigInteger,
  //bigDecimalValue: bigDecimal,
  //timestampValue: timestamp,
}

structure GetExternV2Output {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  integerValue: Integer,
  longValue: Long,
  //byteValue: byte,
  //shortValue: short,
  //floatValue: float,
  //doubleValue: double,
  //bigIntegerValue: bigInteger,
  //bigDecimalValue: bigDecimal,
  //timestampValue: timestamp,
}

// This operation MUST use
// an extern class that can fail
// durring construction.
// This is complicated because
// Dafny constructors MUST NOT fail.
operation UseClassExternV2 {
  input: UseClassExternV2Input,
  output: UseClassExternV2Output,
}

structure UseClassExternV2Input {
  value: String,
}

structure UseClassExternV2Output {
  value: String,
}

// This extern MUST error.
// This is to ensure that
// externs can fail.
operation ExternV2MustError {
  input: ExternV2MustErrorInput,
  output: ExternV2MustErrorOutput,
}

structure ExternV2MustErrorInput{
  value: String,
}
structure ExternV2MustErrorOutput{
  value: String,
}
