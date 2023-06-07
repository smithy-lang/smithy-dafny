// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
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
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  integerValue: Integer,
  longValue: Long,
  //byteValue: Byte,
  //shortValue: Short,
  //floatValue: Float,
  //doubleValue: Double,
  //bigIntegerValue: BigInteger,
  //bigDecimalValue: BigDecimal,
  //timestampValue: Timestamp,
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
  internalConfigString: String,
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
  integerValue: Integer,
  longValue: Long,
  //byteValue: Byte,
  //shortValue: Short,
  //floatValue: Float,
  //doubleValue: Double,
  //bigIntegerValue: BigInteger,
  //bigDecimalValue: BigDecimal,
  //timestampValue: Timestamp,
}
