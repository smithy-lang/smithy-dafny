// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleMultiplemodelsPrimaryprojectImplTest {
    import PrimaryProject
    import opened SimpleMultiplemodelsPrimaryprojectTypes
    import SimpleMultiplemodelsDependencyprojectTypes
    import opened Wrappers
    method{:test} TestPrimaryProject(){
        var client :- expect PrimaryProject.PrimaryProject();
    }

    method TestPrimaryProjectClient(client: IPrimaryProjectClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input1 := SomePrimaryOperationInput();
        var out1 :- expect client.SomePrimaryOperation(input1);

        var input2 := SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationInput();
        var out2 :- expect client.SomeDependencyOperation(input2);
    }
}