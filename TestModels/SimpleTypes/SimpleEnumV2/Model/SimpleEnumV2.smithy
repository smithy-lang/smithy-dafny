$version: "2"

namespace simple.types.enumv2

@aws.polymorph#localService(
  sdkId: "SimpleEnumV2",
  config: SimpleEnumV2Config,
)
service SimpleTypesEnumV2 {
  version: "2021-11-01",
  resources: [],
  operations: [ GetEnumV2 ],
  errors: [],
}

structure SimpleEnumV2Config {}

operation GetEnumV2 {
  input: GetEnumV2Input,
  output: GetEnumV2Output,
}

structure GetEnumV2Input {
  value: Enum
}

structure GetEnumV2Output {
  value: Enum
}

// This is a smithy V2 Enum
enum SimpleEnum {
    FIRST = "0x0014"
    SECOND = "0x0046"
    THIRD = "0x0078"
}