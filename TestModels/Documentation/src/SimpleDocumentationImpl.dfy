// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimpleDocumentationTypes.dfy"
module SimpleDocumentationImpl refines AbstractSimpleDocumentationOperations {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  predicate GetThingEnsuresPublicly(input: GetThingInput , output: Result<GetThingOutput, Error>)
  {true}



  method GetThing ( config: InternalConfig, input: GetThingInput )
    returns (output: Result<GetThingOutput, Error>)

  {
    expect false, "...that you'll fill this in";
  }
}
