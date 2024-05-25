$version: "2"

// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.streaming

@aws.polymorph#localService(
  sdkId: "SimpleStreaming",
  config: SimpleStreamingConfig,
)
service SimpleStreaming {
  version: "2021-11-01",
  operations: [ 
    StreamingBlobInput,
    StreamingBlobOutput,
    StreamingBlobInputAndOutput
     ]
}

structure SimpleStreamingConfig {}

@streaming
blob StreamingBlob

/// Calculates the sum of all bits
operation StreamingBlobInput {
  input := {
    @required
    bits: StreamingBlob
  }
  output := {
    @required
    sum: Integer
  }
}

/// Returns the binary representation of the input.
operation StreamingBlobOutput {
  input := {
    @required
    number: Integer
  }
  output := {
    @required
    binary: StreamingBlob
  }
}

/// Returns input in chunks of the given size.
operation StreamingBlobInputAndOutput {
  input := {
    @required
    bytesIn: StreamingBlob
  }
  output := {
    @required
    bytesOut: StreamingBlob
  }
}