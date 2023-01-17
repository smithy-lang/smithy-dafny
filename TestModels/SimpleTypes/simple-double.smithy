namespace simple.types.double

@aws.polymorph#localService(
  sdkId: "SimpleDouble",
  config: SimpleDoubleConfig,
)
service SimpleTypesDouble {
  version: "2021-11-01",
  resources: [],
  operations: [ GetDouble ],
  errors: [],
}

structure SimpleDoubleConfig {}

operation GetDouble {
  input: GetDoubleInput,
  output: GetDoubleOutput,
}

structure GetDoubleInput {
  value: Double
}

structure GetDoubleOutput {
  value: Double
}
