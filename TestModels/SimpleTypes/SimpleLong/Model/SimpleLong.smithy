namespace simple.types.long

@aws.polymorph#localService(
  sdkId: "SimpleLong",
  config: SimpleLongConfig,
)
service SimpleTypesLong {
  version: "2021-11-01",
  resources: [],
  operations: [ GetLong, GetLongKnownValueTest ],
  errors: [],
}

structure SimpleLongConfig {}

operation GetLong {
  input: GetLongInput,
  output: GetLongOutput,
}

operation GetLongKnownValueTest {
  input: GetLongInput,
  output: GetLongOutput,
}

structure GetLongInput {
  value: Long
}

structure GetLongOutput {
  value: Long
}