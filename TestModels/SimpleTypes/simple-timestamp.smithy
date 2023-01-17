namespace simple.types.timestamp

@aws.polymorph#localService(
  sdkId: "SimpleTimestamp",
  config: SimpleTimestampConfig,
)
service SimpleTypesTimestamp {
  version: "2021-11-01",
  resources: [],
  operations: [ GetTimestamp ],
  errors: [],
}

structure SimpleTimestampConfig {}

operation GetTimestamp {
  input: GetTimestampInput,
  output: GetTimestampOutput,
}

structure GetTimestampInput {
  value: Timestamp
}

structure GetTimestampOutput {
  value: Timestamp
}
