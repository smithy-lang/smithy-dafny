// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleStreamingImpl.dfy"
include "SimpleStreamingImplTest.dfy"

module WrappedSimpleTypesStringTest {
    import WrappedSimpleStreamingService
    import SimpleStreamingImplTest
    import opened Wrappers
    method{:test} TestCountBits() {
        var client :- expect WrappedSimpleStreamingService.WrappedSimpleStreaming();
        SimpleStreamingImplTest.TestCountBits(client);
    }
}
