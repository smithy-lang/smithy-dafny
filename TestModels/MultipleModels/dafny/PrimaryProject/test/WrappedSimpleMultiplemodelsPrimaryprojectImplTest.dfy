// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleMultiplemodelsPrimaryprojectImpl.dfy"
include "SimpleMultiplemodelsPrimaryprojectImplTest.dfy"

module WrappedSimpleMultiplemodelsPrimaryprojectTest {
    import WrappedPrimaryProject
    import SimpleMultiplemodelsPrimaryprojectImplTest
    import opened Wrappers
    method{:test} WrappedPrimaryProjectTest() {
        var client :- expect WrappedPrimaryProject.WrappedPrimaryProject();
        SimpleMultiplemodelsPrimaryprojectImplTest.TestPrimaryProjectClient(client);
    }
}