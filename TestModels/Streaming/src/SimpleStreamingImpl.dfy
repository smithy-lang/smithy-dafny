// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleStreamingTypes.dfy"
include "Chunker.dfy"
module {:options "/functionSyntax:4" } SimpleStreamingImpl refines AbstractSimpleStreamingOperations {

  import Std.Actions
  import Std.Producers
  import Std.Consumers
  import Std.Collections.Seq
  import opened Chunker
  
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
    var counter := new Consumers.FoldingConsumer(Success(0 as int32), SumBits);
    var counterTotalProof := new Consumers.FoldingConsumerTotalActionProof(counter);
 
    var inputReader := input.bits.Reader();
    inputReader.ForEach(counter, counterTotalProof);
    var result := counter.value;

    if result.Success? {
      return Success(CountBitsOutput(sum := result.value));
    } else {
      return Failure(result.error);
    }
  }

  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    var binary := BinaryOfNumber(input.number);
    var binaryStream := new SeqDataStream(binary);
    
    return Success(BinaryOfOutput(binary := binaryStream));
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}

  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    var chunkerStream := new ChunkingStream(input.bytesIn, input.chunkSize);
    
    return Success(ChunksOutput(bytesOut := chunkerStream));
  }

}
