// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleMultiplemodelsDependencyprojectImplTest {
    import DependencyProject
    import opened SimpleMultiplemodelsDependencyprojectTypes
    import opened Wrappers
    method{:test} TestDependencyProject(){
        var client :- expect DependencyProject.DependencyProject();
        TestDependencyProjectClient(client);
    }

    method TestDependencyProjectClient(client: IDependencyProjectClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := SomeDependencyOperationInput();
        var out :- expect client.SomeDependencyOperation(input);
    }
}