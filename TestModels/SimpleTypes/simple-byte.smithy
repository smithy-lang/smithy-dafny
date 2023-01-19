namespace simple.types.byte

@aws.polymorph#localService(
  sdkId: "SimpleByte",
  config: SimpleByteConfig,
)
service SimpleTypesByte {
  version: "2021-11-01",
  resources: [],
  operations: [ GetByte ],
  errors: [],
}

structure SimpleByteConfig {}

operation GetByte {
  input: GetByteInput,
  output: GetByteOutput,
}

structure GetByteInput {
  value: Byte
}

structure GetByteOutput {
  value: Byte
}
