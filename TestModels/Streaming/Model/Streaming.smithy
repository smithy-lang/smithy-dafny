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
    CountBits,
    BinaryOf,
    Chunks
  ]
}

structure SimpleStreamingConfig {}

@suppress(["UnsupportedFeatures"])
@streaming
blob StreamingBlob

/// Calculates the sum of all bits
operation CountBits {
  input := {
    @required
    bits: StreamingBlob
  }
  output := {
    @required
    sum: Integer
  }
  errors: [OverflowError]
}

@error("client")
structure OverflowError {
  @required
  message: String
}

/// Returns the binary representation of the input.
operation BinaryOf {
  input := {
    @required
    number: Integer
  }
  output := {
    @required
    binary: StreamingBlob
  }
}

@range(min: 1)
integer CountingInteger

/// Returns input in chunks of the given size.
operation Chunks {
  input := {
    @required
    bytesIn: StreamingBlob

    @required
    chunkSize: CountingInteger
  }
  output := {
    @required
    bytesOut: StreamingBlob
  }
}