namespace simple.types.string

@aws.polymorph#localService(
  sdkId: "SimpleString",
  config: SimpleStringConfig,
)
service SimpleTypesString {
  version: "2021-11-01",
  resources: [],
  operations: [ GetString ],
  errors: [],
}

structure SimpleStringConfig {}

operation GetString {
  input: GetStringInput,
  output: GetStringOutput,
}

structure GetStringInput {
  value: String
}

structure GetStringOutput {
  value: String
}