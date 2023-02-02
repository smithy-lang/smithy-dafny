// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./Config.dfy"
include "./SimpleResource.dfy"

module SimpleResourcesOperations refines AbstractSimpleResourcesOperations {
  import Config
  import SimpleResource

  type InternalConfig = Config.Config
  
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
