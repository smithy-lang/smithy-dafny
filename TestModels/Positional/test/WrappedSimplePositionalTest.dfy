// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimplePositionalImpl.dfy"
include "SimplePositionalImplTest.dfy"

module WrappedSimplePositionalTest {
    import WrappedSimplePositionalService
    import SimplePositionalImplTest
    import opened Wrappers

    method{:test} TestWrappedClient() {
        var client :- expect WrappedSimplePositionalService.WrappedSimplePositional();

        SimplePositionalImplTest.TestClient(client);
    }
}
