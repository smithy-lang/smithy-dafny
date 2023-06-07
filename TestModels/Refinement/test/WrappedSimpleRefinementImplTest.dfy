// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleRefinementImpl.dfy"
include "SimpleRefinementImplTest.dfy"

module WrappedSimpleRefinementTest {
    import WrappedSimpleRefinementService
    import SimpleRefinementImplTest
    import opened Wrappers
    method{:test} Refinement() {
        var client :- expect WrappedSimpleRefinementService.WrappedSimpleRefinement();
        SimpleRefinementImplTest.TestGetRefinement(client);
        SimpleRefinementImplTest.TestOnlyInput(client);
        SimpleRefinementImplTest.TestOnlyOutput(client);
        SimpleRefinementImplTest.TestReadonlyOperation(client);

    }
}