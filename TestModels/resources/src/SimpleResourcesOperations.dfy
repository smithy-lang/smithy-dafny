// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./Config.dfy"
include "./SimpleResource.dfy"

module SimpleResourcesOperations refines AbstractSimpleResourcesOperations {
  import Config
  import SimpleResource

  // Polymorph's smithydafny demands InternalConfig
  // exist in Operations
  type InternalConfig = Config.Config

  // Polymorph's smithydafny demands ValidInternalConfig? 
  // exist in Operations
  predicate ValidInternalConfig?(config: InternalConfig)
  {
    Config.ValidInternalConfig?(config)
  }

  // Polymorph's smithydafny demands ModifiesInternalConfig
  // exist in Operations
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {
    Config.ModifiesInternalConfig(config)
  }
  
  predicate GetResourcesEnsuresPublicly(
    input: GetResourcesInput,
    output: Result<GetResourcesOutput, Error>
  ) {true}

  method GetResources(
    config: InternalConfig,
    input: GetResourcesInput
  ) returns (
    output: Result<GetResourcesOutput, Error>
  )
    ensures output.Success? ==> output.value.output.ValidState()
  {
    :- Need(Config.ValidInternalConfig?(config),
      Types.SimpleResourceException(
      message := "Simple Resource Client has become invalid")
    );
    :- Need(input.value.Some?,
      Types.SimpleResourceException(
      message := "Input Value MUST be set")
    );
    var resource := new SimpleResource.SimpleResource(
      input.value.value,
      config
     );
     var result: GetResourcesOutput := GetResourcesOutput(
      output := resource
    );
    return Success(result);  
  }
  
}
