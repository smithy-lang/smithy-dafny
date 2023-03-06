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

  predicate CreateExtendableResourceEnsuresPublicly(
    input: CreateExtendableResourceInput,
    output: Result<CreateExtendableResourceOutput, Error>
  ) {true}

  method CreateExtendableResource(
    config: InternalConfig,
    input: CreateExtendableResourceInput
  ) returns (
    output: Result<CreateExtendableResourceOutput, Error>
  )
    ensures
      output.Success?
    ==>
      && output.value.resource.ValidState()
      && fresh(output.value.resource.History)
      && fresh(output.value.resource.Modifies)
  {
    var resource := new ExtendableResource.ExtendableResource.OfName(input.name);
    var result := CreateExtendableResourceOutput(
      resource := resource
    );
    return Success(result);
  }

  predicate UseExtendableResourceEnsuresPublicly(
    input: UseExtendableResourceInput,
    output: Result<UseExtendableResourceOutput, Error>
  ) {true}

  method UseExtendableResource(
    config: InternalConfig,
    input: UseExtendableResourceInput
  ) returns (
    output: Result<UseExtendableResourceOutput, Error>
  )
  {
    var resource := input.resource;
    var data :- resource.GetExtendableResourceData(input.input);
    var result := Types.UseExtendableResourceOutput(
      output := data
    );
    return Success(result);
  }

  predicate UseExtendableResourceAlwaysModeledErrorEnsuresPublicly(
    input: UseExtendableResourceErrorsInput,
    output: Result<GetExtendableResourceErrorsOutput, Error>
  ) {true}

  method UseExtendableResourceAlwaysModeledError(
    config: InternalConfig,
    input: UseExtendableResourceErrorsInput
  ) returns (
    output: Result<GetExtendableResourceErrorsOutput, Error>
  )
  {
    var resource := input.resource;
    var result :- resource.AlwaysModeledError(input.input);
    return Success(result);
  }

  predicate UseExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(
    input: UseExtendableResourceErrorsInput,
    output: Result<GetExtendableResourceErrorsOutput, Error>
  ) {true}

  method UseExtendableResourceAlwaysMultipleErrors(
    config: InternalConfig,
    input: UseExtendableResourceErrorsInput
  ) returns (
    output: Result<GetExtendableResourceErrorsOutput, Error>
  )
  {
    var resource := input.resource;
    var result :- resource.AlwaysMultipleErrors(input.input);
    return Success(result);
  }

  predicate UseExtendableResourceAlwaysOpaqueErrorEnsuresPublicly(
    input: UseExtendableResourceErrorsInput,
    output: Result<GetExtendableResourceErrorsOutput, Error>
  ) {true}

  method UseExtendableResourceAlwaysOpaqueError(
    config: InternalConfig,
    input: UseExtendableResourceErrorsInput
  ) returns (
    output: Result<GetExtendableResourceErrorsOutput, Error>
  )
  {
    var resource := input.resource;
    var result :- resource.AlwaysOpaqueError(input.input);
    return Success(result);
  }  
}
