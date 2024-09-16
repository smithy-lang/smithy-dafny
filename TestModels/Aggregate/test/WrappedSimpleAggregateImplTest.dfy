// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleAggregateImpl.dfy"
include "SimpleAggregateImplTest.dfy"

module WrappedSimpleTypesStringTest {
    import WrappedSimpleAggregateService
    import SimpleAggregateImplTest
    import opened Wrappers
    method{:test} GetAggregate() {
        var client :- expect WrappedSimpleAggregateService.WrappedSimpleAggregate();
        SimpleAggregateImplTest.TestGetAggregate(client);
        SimpleAggregateImplTest.TestGetAggregateKnownValue(client);
    }
}