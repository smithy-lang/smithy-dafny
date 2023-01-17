namespace simple.types.enum

@aws.polymorph#localService(
  sdkId: "SimpleEnum",
  config: SimpleEnumConfig,
)
service SimpleTypesEnum {
  version: "2021-11-01",
  resources: [],
  operations: [ GetEnum ],
  errors: [],
}

structure SimpleEnumConfig {}

operation GetEnum {
  input: GetEnumInput,
  output: GetEnumOutput,
}

structure GetEnumInput {
  value: SimpleEnum
}

structure GetEnumOutput {
  value: SimpleEnum
}

// This is a smithy V1 Enum
@enum([
  {
    name: "FIRST",
    value: "0x0014",
  },
  {
    name: "SECOND",
    value: "0x0046",
  },
  {
    name: "THIRD",
    value: "0x0078",
  },
])
string SimpleEnum