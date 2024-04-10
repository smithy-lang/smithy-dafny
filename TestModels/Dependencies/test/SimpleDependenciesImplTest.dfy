// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../../Constraints/test/Helpers.dfy"

module SimpleDependenciesImplTest {
    import ExtendableResource
    import SimpleConstraints
    import SimpleConstraintsTestHelpers = Helpers
    import SimpleDependencies
    import SimpleDependenciesTypes
    import SimpleExtendableResourcesTypes
    import SimpleResourcesTypes
    import opened Wrappers
    
    method{:test} TestDependenciesWithDefaultConfig()
    {        
        var client :- expect SimpleDependencies.SimpleDependencies();
        TestGetSimpleResource(client);
        TestUseSimpleResource(client);
        TestUseLocalExtendableResource(client);
        TestUseLocalConstraintsService(client);
        TestLocalExtendableResourceAlwaysModeledError(client);
        TestLocalExtendableResourceAlwaysMultipleErrors(client);
        TestLocalExtendableResourceAlwaysOpaqueError(client);
    }

    method{:test} TestDependenciesWithCustomConfig()
    {        
      var extendableResourceReferenceToAssign := new ExtendableResource.ExtendableResource();
      var simpleConstraintsServiceReferenceToAssign :- expect SimpleConstraints.SimpleConstraints();

      var customConfig := SimpleDependenciesTypes.SimpleDependenciesConfig(
        simpleResourcesConfig := Some(SimpleResourcesTypes.SimpleResourcesConfig(
          name := "default"
        )),
        extendableResourceReference := Some(extendableResourceReferenceToAssign),
        simpleConstraintsServiceReference := Some(simpleConstraintsServiceReferenceToAssign),
        specialString := Some("bw1and10")
      );

      var client :- expect SimpleDependencies.SimpleDependencies(config := customConfig);
        TestGetSimpleResource(client);
        TestUseSimpleResource(client);
        TestUseLocalExtendableResource(client);
        TestUseLocalConstraintsService(client);
        TestLocalExtendableResourceAlwaysModeledError(client);
        TestLocalExtendableResourceAlwaysMultipleErrors(client);
        TestLocalExtendableResourceAlwaysOpaqueError(client);
    }
    
    method TestGetSimpleResource(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var input := SimpleResourcesTypes.GetResourcesInput(value := Some("anyInput"));
      var res :- expect client.GetSimpleResource(input := input);    
    }

    method TestUseSimpleResource(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var resourceDataInput: SimpleResourcesTypes.GetResourceDataInput := SimpleResourcesTypes.GetResourceDataInput(
        blobValue := Some([0, 1]),
        booleanValue := Some(true),
        stringValue := Some("anyString"),
        integerValue := Some(123),
        longValue := Some(123)
      );

      var getResourcesInput := SimpleResourcesTypes.GetResourcesInput(value := Some("anyInput"));
      var getResourcesOutput :- expect client.GetSimpleResource(input := getResourcesInput);

      var input := SimpleDependenciesTypes.UseSimpleResourceInput(
        value := getResourcesOutput.output,
        input := resourceDataInput
      );

      var res :- expect client.UseSimpleResource(input := input);
    }

    method TestUseLocalConstraintsService(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var resourceDataInput := SimpleConstraintsTestHelpers.GetValidInput();
      var res :- expect client.UseLocalConstraintsService(resourceDataInput);
      expect res.MyString.Some?;
      expect res.MyString.value == "bw1and10";
    }

    method TestUseLocalExtendableResource(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var resourceDataInput := SimpleExtendableResourcesTypes.GetExtendableResourceDataInput(
        blobValue := Some([1]),
        booleanValue := Some(true),
        stringValue := Some("Some"),
        integerValue := Some(1),
        longValue := Some(1)
      );

      var res :- expect client.UseLocalExtendableResource(input := resourceDataInput);
    }

    method TestLocalExtendableResourceAlwaysModeledError(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var errorInput := SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput(
        value := Option.Some("Some")
      );
      var errorOutput := client.LocalExtendableResourceAlwaysModeledError(errorInput);   
      expect errorOutput.Failure?;
      expect errorOutput.error.SimpleExtendableResources?;
      expect errorOutput.error.SimpleExtendableResources.SimpleExtendableResourcesException?;
    }

    method TestLocalExtendableResourceAlwaysMultipleErrors(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var errorInput := SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput(
        value := Option.Some("Some")
      );
      var errorOutput := client.LocalExtendableResourceAlwaysMultipleErrors(errorInput);   
      expect errorOutput.Failure?;
      expect errorOutput.error.SimpleExtendableResources?;
      expect errorOutput.error.SimpleExtendableResources.CollectionOfErrors?;
    }

    method TestLocalExtendableResourceAlwaysOpaqueError(
      client: SimpleDependenciesTypes.ISimpleDependenciesClient
    )
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      var errorInput := SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput(
        value := Option.Some("Some")
      );
      var errorOutput := client.LocalExtendableResourceAlwaysNativeError(errorInput);   
      expect errorOutput.Failure?;
      expect errorOutput.error.SimpleExtendableResources?;
      expect errorOutput.error.SimpleExtendableResources.Opaque?;
    }

}
