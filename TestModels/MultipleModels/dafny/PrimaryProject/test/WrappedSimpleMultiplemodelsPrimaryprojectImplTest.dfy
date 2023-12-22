// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleMultiplemodelsPrimaryprojectImpl.dfy"
include "SimpleMultiplemodelsPrimaryprojectImplTest.dfy"

module WrappedSimpleMultiplemodelsPrimaryprojectTest {
    import WrappedSimpleMultiplemodelsPrimaryprojectService
    import SimpleMultiplemodelsPrimaryprojectImplTest
    import opened Wrappers
    method{:test} WrappedPrimaryProject() {
        var client :- expect WrappedSimpleMultiplemodelsPrimaryprojectService.WrappedPrimaryProject();
        SimpleMultiplemodelsPrimaryprojectImplTest.TestPrimaryProjectClient(client);
    }
}