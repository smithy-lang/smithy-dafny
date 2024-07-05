// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleStreamingTypes.dfy"
module SimpleStreamingImpl refines AbstractSimpleStreamingOperations {

  import opened Std.Aggregators

  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  predicate CountBitsEnsuresPublicly(input: CountBitsInput , output: Result<CountBitsOutput, Error>)
  {true}

  method CountBits ( config: InternalConfig , input: CountBitsInput )
    returns (output: Result<CountBitsOutput, Error>)
  {
    // TODO: actually count bits. Just guessing the average (like guessing all C's on a test :) 
    var counter := new Folder(0, (x, y) => x + 4);

    ForEach(input.bits, counter);
    
    return Success(CountBitsOutput(sum := counter.value));
  }


  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    // TODO: Actually compute the binary
    var fakeBinary: seq<bytes> := [[12], [34, 56]];
    var fakeBinaryEnumerator := new SeqEnumerator(fakeBinary);
    
    return Success(BinaryOfOutput(binary := fakeBinaryEnumerator));
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}


  class Chunker extends Pipeline<bytes, bytes> {

    const chunkSize: int32
    var chunkBuffer: bytes

    constructor(upstream: Enumerator<bytes>, chunkSize: int32)
    {
      this.buffer := new Collector<bytes>();
      this.upstream := upstream;

      this.chunkSize := chunkSize;
      chunkBuffer := [];
    }

    method {:verify false} Process(event: Option<bytes>, a: Accumulator<bytes>)
    {
      match event {
        case Some(bits) => {
          chunkBuffer := chunkBuffer + bits;
        }
      }

      while chunkSize as nat <= |chunkBuffer| {
        var _ := a.Invoke(chunkBuffer[..chunkSize]);
        chunkBuffer := chunkBuffer[chunkSize..];
      }
      
      if event == None {
        if 0 < |chunkBuffer| {
          var _ := a.Invoke(chunkBuffer);
        }
      }
    }
  }

  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var chunker := new Chunker(input.bytesIn, input.chunkSize);

    return Success(ChunksOutput(bytesOut := chunker));
  }





  method ChunksAlt ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var outStream := SomeOtherServiceOp(input.bytesIn);

    return Success(ChunksOutput(bytesOut := outStream));
  }

  method SomeOtherServiceOp( input: StreamingBlob ) returns (r: StreamingBlob) {
    // Imagine this was external
    r := new SeqEnumerator([]);
  }
}
