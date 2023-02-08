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
  {
    var resource := input.value;
    var maybeData := resource.GetResourceData(input.input);
    if (maybeData.Success?) {
      var result := UseExtendableResourcesOutput(
        output := maybeData.Extract()
      );
      return Success(result);
    } else {
      return maybeData.PropagateFailure<UseExtendableResourcesOutput>();
    }
  }
}
