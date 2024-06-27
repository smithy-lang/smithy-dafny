// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../Model/SimplePositionalTypes.dfy"
include "./SimpleResource.dfy"
module SimplePositionalImpl refines AbstractSimplePositionalOperations {
  import SimpleResource

  datatype Config = Config
  type InternalConfig = Config
    
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  predicate GetResourceEnsuresPublicly(input: GetResourceInput , output: Result<GetResourceOutput, Error>)
  {true}



  method GetResource ( config: InternalConfig , input: GetResourceInput )
    returns (output: Result<GetResourceOutput, Error>)

  {
    var resource := new SimpleResource.SimpleResource(
      input.name
    );
    var result: GetResourceOutput := GetResourceOutput(
      output := resource
    );
    return Success(result);  
  }


  predicate GetResourcePositionalEnsuresPublicly(input: GetResourceInput , output: Result<ISimpleResource, Error>)
  {true}



  method GetResourcePositional ( config: InternalConfig , input: GetResourceInput )
    returns (output: Result<ISimpleResource, Error>)

  {
    var resource := new SimpleResource.SimpleResource(
      input.name
    );
    // @positional allows use to return the result without the output structure
    return Success(resource);  
  }
}
