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
    var counter := new Consumers.FoldingConsumer(0, SumBits);
    var counterTotalProof := new Consumers.FoldingConsumerTotalActionProof(counter);
 
    input.bits.ForEachRemaining(counter, counterTotalProof);

    // Should really have the FoldingConsumer fail instead,
    // but this is a simpler correct approach.
    if 0 <= counter.value < INT32_MAX_LIMIT {
      return Success(CountBitsOutput(sum := counter.value as int32));
    } else {
      return Failure(OverflowError(message := "Ah crap"));
    }
  }

  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    var binary := BinaryOfNumber(input.number);
    var binaryStream := new SeqDataStream(binary, 3 as BoundedInts.uint64);
    
    return Success(BinaryOfOutput(binary := binaryStream));
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}

  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)
  {
    // TODO: for now
    assume {:axiom} input.bytesIn.history == [];
    var chunker := new Chunker(input.chunkSize);
    var chunkerStream := new MappedDataStream(input.bytesIn, chunker);
    
    return Success(ChunksOutput(bytesOut := chunkerStream));
  }

}
