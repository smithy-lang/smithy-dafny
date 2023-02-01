namespace simple.types.bigInteger

@aws.polymorph#localService(
  sdkId: "SimpleBigInteger",
  config: SimpleBigIntegerConfig,
)
service SimpleTypesBigInteger {
  version: "2021-11-01",
  resources: [],
  operations: [ GetBigInteger ],
  errors: [],
}

structure SimpleBigIntegerConfig {}

operation GetBigInteger {
  input: GetBigIntegerInput,
  output: GetBigIntegerOutput,
}

structure GetBigIntegerInput {
  value: BigInteger
}

structure GetBigIntegerOutput {
  value: BigInteger
}