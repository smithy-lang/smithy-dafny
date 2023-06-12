// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleConstraintsImpl.dfy"
include "SimpleConstraintsImplTest.dfy"

module WrappedSimpleConstraintsTest {
    import WrappedSimpleConstraintsService
    import SimpleConstraintsImplTest
    import opened Wrappers
    method{:test} GetConstraints() {
        var client :- expect WrappedSimpleConstraintsService.WrappedSimpleConstraints();
        SimpleConstraintsImplTest.TestGetConstraintWithValidInputs(client);
    }
}