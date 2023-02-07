// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypes.dfy"
include "./ExtendableResource.dfy"

module SimpleExtendableResourcesOperations refines AbstractSimpleExtendableResourcesOperations {
  import ExtendableResource

  datatype Config = Config()
    
  type InternalConfig = Config

  predicate method ValidInternalConfig?(
    config: InternalConfig
  ) {true}
    
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}  

  predicate UseExtendableResourcesEnsuresPublicly(
    input: UseExtendableResourcesInput,
    output: Result<UseExtendableResourcesOutput, Error>
  ) {true}

  method UseExtendableResources(
    config: InternalConfig,
    input: UseExtendableResourcesInput
  ) returns (
    output: Result<UseExtendableResourcesOutput, Error>
  )
    ensures output.Success? ==> output.value.output.ValidState()
  {
    var resource := new ExtendableResource.ExtendableResource();
    var result := UseExtendableResourcesOutput(
      output := resource
    );
    return Success(result);
  }
}
