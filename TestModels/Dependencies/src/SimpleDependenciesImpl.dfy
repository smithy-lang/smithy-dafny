// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDependenciesTypes.dfy"

module SimpleDependenciesImpl refines AbstractSimpleDependenciesOperations {
  import ExtendableResource
  import SimpleConstraintsTypes
  import SimpleExtendableResourcesTypes
  import SimpleResources

  datatype Config = Config(
    nameonly simpleResourcesConfig: SimpleResourcesTypes.SimpleResourcesConfig,
    nameonly simpleConstraintsServiceReference: SimpleConstraintsTypes.ISimpleConstraintsClient,
    nameonly extendableResourceReference: SimpleExtendableResourcesTypes.IExtendableResource,
    nameonly specialString: SimpleConstraintsTypes.MyString
  )

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
  {
    && config.simpleConstraintsServiceReference.ValidState()
    && config.extendableResourceReference.ValidState()
  }

  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {
    config.simpleConstraintsServiceReference.Modifies
    + config.extendableResourceReference.Modifies
  }

  predicate GetSimpleResourceEnsuresPublicly(
    input: SimpleResourcesTypes.GetResourcesInput,
    output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
  {
    true
  }

  predicate UseSimpleResourceEnsuresPublicly(
    input: UseSimpleResourceInput,
    output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
  {
    true
  }

  predicate UseLocalConstraintsServiceEnsuresPublicly(
    input: SimpleConstraintsTypes.GetConstraintsInput,
    output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
  {
    true
  }

  predicate UseLocalExtendableResourceEnsuresPublicly(
    input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput,
    output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
  {
    true
  }

  predicate LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(
    input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput,
    output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    true
  }

  predicate LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(
    input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput,
    output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    true
  }

  predicate LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(
    input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput,
    output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    true
  }

  method GetSimpleResource( config: InternalConfig, input: SimpleResourcesTypes.GetResourcesInput )
    returns (output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
  {
    expect input.value.Some?;

    var simpleResourcesConfig := config.simpleResourcesConfig;

    var client: SimpleResources.SimpleResourcesClient :- expect SimpleResources.SimpleResources(
      simpleResourcesConfig
    );

    var res :- expect client.GetResources(input);
    return Success(res);
  }
  
  method UseSimpleResource( config: InternalConfig, input: UseSimpleResourceInput )
    returns (output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
  {
    var reference := input.value;
    var getResourceDataInput := input.input;

    var res: SimpleResourcesTypes.GetResourceDataOutput :- expect reference.GetResourceData(input := getResourceDataInput);
    return Success(res);
  }

  method UseLocalConstraintsService( config: InternalConfig, input: SimpleConstraintsTypes.GetConstraintsInput )
    returns (output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
  {
    var simpleConstraintsService := config.simpleConstraintsServiceReference;
    var res :- expect simpleConstraintsService.GetConstraints(input);
    return Success(res);
  }

  method UseLocalExtendableResource( config: InternalConfig, input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput )
    returns (output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
  {
    var reference := config.extendableResourceReference;
    var callInput := SimpleExtendableResourcesTypes.UseExtendableResourceInput(
      resource := reference,
      input := input
    );

    var res :- expect reference.GetExtendableResourceData(input := input);

    var toReturn := SimpleExtendableResourcesTypes.UseExtendableResourceOutput(
      output := res
    );

    return Success(toReturn);
  }

  method LocalExtendableResourceAlwaysModeledError( config: InternalConfig, input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
    returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    var extendableResourceError := SimpleExtendableResourcesTypes.SimpleExtendableResourcesException(
      message := "Hard Coded Exception in src/dafny"
    );
    var dependenciesError := Error.SimpleExtendableResources(extendableResourceError);
    return Failure(dependenciesError);
  }

    method LocalExtendableResourceAlwaysMultipleErrors( config: InternalConfig, input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
    returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    var nestedExtendableResourceError := SimpleExtendableResourcesTypes.SimpleExtendableResourcesException(
      message := "Hard Coded Modeled Exception in Collection"
    );
    var nestedExtendableResourceError2 := SimpleExtendableResourcesTypes.SimpleExtendableResourcesException(
      message := "msg no 2"
    );
    var collectionOfExtendableResourceErrors := SimpleExtendableResourcesTypes.CollectionOfErrors(
      [nestedExtendableResourceError, nestedExtendableResourceError2],
      message := "2 Somethings"
    );
    var dependenciesError := Error.SimpleExtendableResources(collectionOfExtendableResourceErrors);
    return Failure(dependenciesError);
  }

    method LocalExtendableResourceAlwaysNativeError( config: InternalConfig, input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
    returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
  {
    var obj: object := new ExtendableResource.OpaqueMessage();
    var extendableResourceError := SimpleExtendableResourcesTypes.Opaque(obj);
    var dependenciesError := Error.SimpleExtendableResources(extendableResourceError);
    return Failure(dependenciesError);
  }

}
