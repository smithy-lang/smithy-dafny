// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleUnionImpl.dfy"
include "SimpleUnionImplTest.dfy"

module WrappedSimpleUnionTest {
    import WrappedSimpleUnionService
    import SimpleUnionImplTest
    import opened Wrappers
    method{:test} TestUnion() {
        var client :- expect WrappedSimpleUnionService.WrappedSimpleUnion();
        SimpleUnionImplTest.TestMyUnionInteger(client);
        SimpleUnionImplTest.TestMyUnionString(client);
        SimpleUnionImplTest.TestKnownValueUnionString(client);

    }
}
