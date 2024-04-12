// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.bigDecimal

@aws.polymorph#localService(
  sdkId: "SimpleBigDecimal",
  config: SimpleBigDecimalConfig,
)
service SimpleTypesBigDecimal {
  version: "2021-11-01",
  resources: [],
  operations: [ GetBigDecimal ],
  errors: [],
}

structure SimpleBigDecimalConfig {}

operation GetBigDecimal {
  input: GetBigDecimalInput,
  output: GetBigDecimalOutput,
}

structure GetBigDecimalInput {
  value: BigDecimal
}

structure GetBigDecimalOutput {
  value: BigDecimal
}
