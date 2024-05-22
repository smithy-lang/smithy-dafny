// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

$version: "2"

namespace simple.streaming

@aws.polymorph#localService(
  sdkId: "SimpleStreaming",
  config: SimpleStreamingConfig,
)
service SimpleStreaming {
  version: "2021-11-01",
  resources: [],
  operations: [
    Read,
    Write,
  ],
  errors: [],
}

structure SimpleStreamingConfig {}

operation Read {
  input: ReadInput,
  output: ReadOutput,
}

operation Write {
  input: WriteInput,
  output: WriteOutput,
}

structure ReadInput {
  value: String
}

structure ReadOutput {
  @required
  value: StreamingBlob
}

structure WriteInput {
  @required
  value: StreamingBlob
}

structure WriteOutput {
  value: String
}

@streaming
blob StreamingBlob
