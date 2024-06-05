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

    constructor() 
      ensures fresh(Repr)
    {
      sumSoFar := 0;
      Repr := {};
    }

    method Call(value: StreamEvent<seq<uint8>, Error>) returns (nothing: ()) 
      modifies Repr
    {
      assume this in Repr;
      match value {
        case Some(bits) => {
          // TODO: actually count bits. Just guessing the average (like guessing all C's on a test :) 
          assume sumSoFar < 10000;
          sumSoFar := sumSoFar + 4;
        }
        case None => {}
      }
      return ();
    }
  }


  method CountBits ( config: InternalConfig , input: CountBitsInput )
    returns (output: Result<CountBitsOutput, Error>)
  {
    var counter := new BitCounter();

    input.bits.ForEach(counter);
    
    return Success(CountBitsOutput(sum := counter.sumSoFar));
  }


  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    // TODO: Actually compute the binary
    var fakeBinary := [Some(Success([12])), Some(Success([34, 56]))];
    var fakeBinaryIter := new SeqEnumerator(fakeBinary);
    
    var outStream := new SimpleStream<StreamEvent<seq<uint8>, Error>>(fakeBinaryIter);

    return Success(BinaryOfOutput(binary := outStream));
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}


  class Chunker extends BlockingPipeline<BytesEvent, BytesEvent> {

    const chunkSize: int32
    var chunkBuffer: seq<uint8>

    constructor(upstream: StreamingBlob, chunkSize: int32)
    {
      this.buffer := new CollectingAction<BytesEvent>();
      this.upstream := upstream;
      this.chunkSize := chunkSize;
      chunkBuffer := [];
    }

    method {:verify false} Process(event: BytesEvent, a: Action<BytesEvent, ()>)
    {
      match event {
        case Some(Success(bits)) => {
          chunkBuffer := chunkBuffer + bits;
        }
      }

      while chunkSize as nat <= |chunkBuffer| {
        var _ := a.Call(Some(Success(chunkBuffer[..chunkSize])));
        chunkBuffer := chunkBuffer[chunkSize..];
      }
      if event == None || event.value.Failure? {
        if 0 < |chunkBuffer| {
          var _ := a.Call(Some(Success(chunkBuffer)));
        }
        var _ := a.Call(event);
      }
    }
  }

  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var chunker := new Chunker(input.bytesIn, input.chunkSize);

    // TODO: Connect streams together for flow control.
    // May want to wrap Chunker as a transform that offers flow control from the downstream.
    // Can we create the right kind of output stream (e.g. InputStream vs Publisher)
    // based on what kind of input stream we were passed?

    return Success(ChunksOutput(bytesOut := chunker));
  }





  method ChunksAlt ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var outStream := SomeOtherServiceOp(input.bytesIn);

    return Success(ChunksOutput(bytesOut := outStream));
  }

  method SomeOtherServiceOp( input: Stream'<seq<uint8>> ) returns (r: Stream'<seq<uint8>>) {
    // Imagine this was external
    r := new EmptyStream();
  }
}
