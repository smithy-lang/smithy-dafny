// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleStreamingTypes.dfy"
module SimpleStreamingImpl refines AbstractSimpleStreamingOperations {
  import opened StandardLibrary.Actions

  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  predicate CountBitsEnsuresPublicly(input: CountBitsInput , output: Result<CountBitsOutput, Error>)
  {true}

  class BitCounter extends Action<StreamEvent<seq<uint8>, Error>, ()> {

    var sumSoFar: int32
    const outStream: SimpleStream<StreamEvent<int32, Error>>

    constructor(outStream: SimpleStream<StreamEvent<int32, Error>>) 
      ensures fresh(Repr)
    {
      sumSoFar := 0;
      this.outStream := outStream;
      Repr := {};
    }

    method Call(value: StreamEvent<seq<uint8>, Error>) returns (nothing: ()) 
      modifies Repr
    {
      assume this in Repr;
      assume outStream.Repr <= Repr;
      match value {
        case Some(bits) => {
          // TODO: actually count bits. Just guessing the average (like guessing all C's on a test :) 
          assume sumSoFar < 10000;
          sumSoFar := sumSoFar + 4;
        }
        case None => {
          outStream.Put(Some(Success(sumSoFar)));
        }
      }
      return ();
    }
  }


  method CountBits ( config: InternalConfig , input: CountBitsInput )
    returns (output: Result<CountBitsOutput, Error>)
  {
    var outStream := new SimpleStream<StreamEvent<int32, Error>>();
    var counter := new BitCounter(outStream);
    Subscribe(input.bits, counter);
    return Success(CountBitsOutput(sum := outStream));
  }


  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    // TODO: Actually compute the binary
    var fakeBinary := [Success([12]), Success([34, 56])];
    var fakeBinaryIter := new SeqEnumerator(fakeBinary);
    
    var outStream := new LazyStream<Result<seq<uint8>, Error>>(fakeBinaryIter);

    return Success(BinaryOfOutput(binary := outStream));
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}


  class Chunker extends Action<StreamEvent<seq<uint8>, Error>, ()> {

    const outStream: SimpleStream<StreamEvent<seq<uint8>, Error>>
    const chunkSize: int32
    var buffer: seq<uint8>

    constructor(chunkSize: int32, outStream: SimpleStream<StreamEvent<seq<uint8>, Error>>)
      ensures fresh(Repr) 
    {
      this.outStream := outStream;
      this.chunkSize := chunkSize;
      Repr := {};
      buffer := [];
    }

    method {:verify false} Call(value: StreamEvent<seq<uint8>, Error>) returns (nothing: ())
      modifies Repr
    {
      match value {
        case Some(Success(bits)) => {
          buffer := buffer + bits;
        }
      }
      while chunkSize as nat <= |buffer| {
        outStream.Put(Some(Success(buffer[..chunkSize])));
        buffer := buffer[chunkSize..];
      }
      if value == None || value.value.Failure? {
        if 0 < |buffer| {
          outStream.Put(Some(Success(buffer)));
        }
        outStream.Put(value);
      }
      return ();
    }
  }

  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var outStream := new SimpleStream<StreamEvent<seq<uint8>, Error>>();
    var chunker := new Chunker(input.chunkSize, outStream);
    Subscribe(input.bytesIn, chunker);

    // TODO: Connect streams together

    return Success(ChunksOutput(bytesOut := outStream));
  }
}
