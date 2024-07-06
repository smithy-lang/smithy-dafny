$version: "2"

// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.streaming



// TODO: Call streaming operations on SDKs from Dafny
//       Sync Dafny client good enough, or do we start supporting async code in Dafny?
// TODO: model the Java ESDK EncryptingInputStream/EncryptingOutputStream type operations
//       Definitely possible, may not be very directly supported with AsyncRequestBody/AsyncResponseTransformer
// TODO: event streams (i.e. unions) as well
// TODO: @requiresLength as well

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

/// Returns input in chunks of the given size.
operation Chunks {
  input := {
    @required
    bytesIn: StreamingBlob

    @required
    @range(min: 1)
    chunkSize: Integer
  }
  output := {
    @required
    bytesOut: StreamingBlob
  }
}

/// Returns input in chunks of the given size.
operation Chunks {
  input := {
    @required
    bytesIn: StreamingBlob

    @required
    @range(min: 1)
    chunkSize: Integer
  }
  output := {
    @required
    bytesOut: StreamingBlob
  }
}
