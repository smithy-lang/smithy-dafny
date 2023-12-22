// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleMultiplemodelsDependencyprojectImpl.dfy"
include "SimpleMultiplemodelsDependencyprojectImplTest.dfy"

module WrappedSimpleMultiplemodelsDependencyprojectTest {
    import WrappedSimpleMultiplemodelsDependencyprojectService
    import SimpleMultiplemodelsDependencyprojectImplTest
    import opened Wrappers
    method{:test} WrappedDependencyProject() {
        var client :- expect WrappedSimpleMultiplemodelsDependencyprojectService.WrappedDependencyProject();
        SimpleMultiplemodelsDependencyprojectImplTest.TestDependencyProjectClient(client);
    }
}