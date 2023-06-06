namespace simple.streaming

@aws.polymorph#localService(
  sdkId: "Streaming",
  config: StreamingConfig,
)
service Streaming {
  version: "2021-11-01",
  resources: [],
  operations: [ GetBlob ],
  errors: [],
}

structure StreamingConfig {}

operation GetBlob {
  input: GetBlobInput,
  output: GetBlobOutput,
}

structure GetBlobInput {
  value: StreamingBlob
}

structure GetBlobOutput {
  value: StreamingBlob
}

@streaming
blob StreamingBlob