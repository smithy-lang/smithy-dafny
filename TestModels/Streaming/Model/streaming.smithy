$version: "2"

// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.streaming


// QUESTIONS:
// 1. Priority of async clients/operations? Add later?
//    a. Java ESDK only offers InputStream/OutputStream wrappers
//    J: Interfaces more important
// 2. Can we depend on AWS SDK core libraries for streaming types for now?
//    a. Yes we want to break the dependency eventually
//    J: v3 S3EC Java does as well. Crypto Primitives?
//    For now will propose reusing SDK libraries in doc/poc
// 3. Asymmetry of input vs. output streams? Other languages are inconsistent (Java and IIRC Go uses different types)
//    Asymmetric would definitely be easier for Dafny synchronous output
//    TODO: try others to see if they actually don't handle sharing a structure as input and output
 

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