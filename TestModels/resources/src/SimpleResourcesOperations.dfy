// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./SimpleResource.dfy"

module SimpleResourcesOperations refines AbstractSimpleResourcesOperations {
  import SimpleResource

  datatype Config = Config(
    nameonly name: string
  )

  type InternalConfig = Config
    
  predicate method ValidInternalConfig?(config: InternalConfig)
  {
    && |config.name| > 0
  }

  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  
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
    :- Need(ValidInternalConfig?(config),
      Types.SimpleResourcesException(
      message := "Simple Resource Client has become invalid")
    );
    var resource := new SimpleResource.SimpleResource(
      input.value,
      config.name
    );
    var result: GetResourcesOutput := GetResourcesOutput(
      output := resource
    );
    return Success(result);  
  }
  
}
