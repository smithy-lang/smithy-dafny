namespace simple.union

@aws.polymorph#localService(
  sdkId: "SimpleUnion",
  config: SimpleUnionConfig,
)
service SimpleUnion {
  version: "2021-11-01",
  operations: [ GetUnion ]
}

structure SimpleUnionConfig {}

operation GetUnion {
  input: GetUnionInput,
  output: GetUnionOutput
}

structure GetUnionInput {
    union: MyUnion
}

structure GetUnionOutput {
    union: MyUnion
}

union MyUnion {
    IntegerValue: Integer,
    StringValue: String
}