// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleMultiplemodelsDependencyprojectImpl.dfy"
include "SimpleMultiplemodelsDependencyprojectImplTest.dfy"

module WrappedSimpleMultiplemodelsDependencyprojectTest {
    import WrappedDependencyProject
    import SimpleMultiplemodelsDependencyprojectImplTest
    import opened Wrappers
    method{:test} WrappedDependencyProjectTest() {
        var client :- expect WrappedDependencyProject.WrappedDependencyProject();
        SimpleMultiplemodelsDependencyprojectImplTest.TestDependencyProjectClient(client);
    }
}