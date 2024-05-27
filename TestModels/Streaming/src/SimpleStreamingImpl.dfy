// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleStreamingTypes.dfy"
module SimpleStreamingImpl refines AbstractSimpleStreamingOperations {
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
    expect false, "...that you'll fill this in";
  }


  predicate BinaryOfEnsuresPublicly(input: BinaryOfInput , output: Result<BinaryOfOutput, Error>)
  {true}



  method BinaryOf ( config: InternalConfig , input: BinaryOfInput )
    returns (output: Result<BinaryOfOutput, Error>)

  {
    expect false, "...that you'll fill this in";
  }


  predicate ChunksEnsuresPublicly(input: ChunksInput , output: Result<ChunksOutput, Error>)
  {true}



  method Chunks ( config: InternalConfig , input: ChunksInput )
    returns (output: Result<ChunksOutput, Error>)

  {
    expect false, "...that you'll fill this in";
  }
}
