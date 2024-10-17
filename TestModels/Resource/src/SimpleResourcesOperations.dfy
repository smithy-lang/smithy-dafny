// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./SimpleResource.dfy"
include "./MutableResource.dfy"

module SimpleResourcesOperations refines AbstractSimpleResourcesOperations {
  import SimpleResource
  import MutableResource

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
    var resource := new SimpleResource.SimpleResource(
      input.value,
      config.name
    );
    var result: GetResourcesOutput := GetResourcesOutput(
      output := resource
    );
    return Success(result);
  }

  predicate GetMutableResourcesEnsuresPublicly(input: GetMutableResourcesInput , output: Result<GetMutableResourcesOutput, Error>)
  {true}

  method GetMutableResources ( config: InternalConfig , input: GetMutableResourcesInput )
    returns (output: Result<GetMutableResourcesOutput, Error>)
  {
    var resource := new MutableResource.MutableResource(
      input.value,
      config.name
    );
    var result: GetMutableResourcesOutput := GetMutableResourcesOutput(
      output := resource
    );
    return Success(result);
  }

}
