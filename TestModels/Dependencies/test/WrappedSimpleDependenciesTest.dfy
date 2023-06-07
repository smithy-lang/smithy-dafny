// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleDependenciesImpl.dfy"
include "SimpleDependenciesImplTest.dfy"

module WrappedSimpleDependenciesTest {
    import WrappedSimpleDependenciesService
    import SimpleDependenciesImplTest
    import SimpleDependenciesTypes
    import ExtendableResource
    import SimpleDependencies
    import SimpleResourcesTypes
    import SimpleConstraints
    import opened Wrappers
    method{:test} TestDependenciesWithDefaultConfig() {
        var client :- expect WrappedSimpleDependenciesService.WrappedSimpleDependencies();
        SimpleDependenciesImplTest.TestGetSimpleResource(client);
        SimpleDependenciesImplTest.TestUseSimpleResource(client);
        SimpleDependenciesImplTest.TestUseLocalConstraintsService(client);
        SimpleDependenciesImplTest.TestUseLocalExtendableResource(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysModeledError(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysMultipleErrors(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysOpaqueError(client);
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
        SimpleDependenciesImplTest.TestGetSimpleResource(client);
        SimpleDependenciesImplTest.TestUseSimpleResource(client);
        SimpleDependenciesImplTest.TestUseLocalConstraintsService(client);
        SimpleDependenciesImplTest.TestUseLocalExtendableResource(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysModeledError(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysMultipleErrors(client);
        SimpleDependenciesImplTest.TestLocalExtendableResourceAlwaysOpaqueError(client);
    }
}