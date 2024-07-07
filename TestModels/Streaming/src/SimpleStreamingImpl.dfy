// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleStreamingTypes.dfy"
module SimpleStreamingImpl refines AbstractSimpleStreamingOperations {

  import opened Std.Aggregators
  import Seq

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
    var counter := new Folder<bytes, int>(0, (sum, byte) => sum + BytesBitCount(byte));
 
    ForEach(input.bits, counter);

    // Should really have the Folder fail instead,
    // but this is a simpler correct approach.
    if 0 <= counter.value < INT32_MAX_LIMIT {
      return Success(CountBitsOutput(sum := counter.value as int32));
    } else {
      return Failure(OverflowError(message := "Ah crap"));
    }
  }

  function method BytesBitCount(b: bytes): int {
    Seq.FoldLeft((sum, byte) => sum + BitCount(byte), 0 as int, b)
  }

  function method BitCount(x: uint8): int {
    if x == 0 then
      0
    else if x % 1 == 1 then
      1 + BitCount(x / 2)
    else
      BitCount(x / 2)
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

    const chunkSize: CountingInteger
    var chunkBuffer: bytes

    constructor(upstream: Enumerator<bytes>, chunkSize: CountingInteger)
    {
      this.buffer := new Collector<bytes>();
      this.upstream := upstream;

      this.chunkSize := chunkSize;
      chunkBuffer := [];
    }

    method Process(event: Option<bytes>, a: Accumulator<bytes>)
      requires Valid()
      requires a.Valid()
      requires Repr !! a.Repr
      modifies Repr, a.Repr
      ensures a.ValidAndDisjoint()
    {
      assert this in Repr;
      assert this !in a.Repr;
      match event {
        case Some(bits) => {
          chunkBuffer := chunkBuffer + bits;
        }
        case None => return;
      }

      while chunkSize as int <= |chunkBuffer| 
        invariant a.ValidAndDisjoint()
      {
        a.Accept(chunkBuffer[..chunkSize]);
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
