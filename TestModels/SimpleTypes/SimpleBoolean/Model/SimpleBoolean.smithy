namespace simpletypes.boolean

@aws.polymorph#localService(
  sdkId: "SimpleBoolean",
  config: SimpleBooleanConfig,
)
service SimpleBoolean {
  version: "2021-11-01",
  resources: [],
  operations: [ GetBoolean ],
  errors: [],
}

structure SimpleBooleanConfig {}

operation GetBoolean {
  input: GetBooleanInput,
  output: GetBooleanOutput,
}

structure GetBooleanInput {
  value: Boolean
}

structure GetBooleanOutput {
  value: Boolean
}