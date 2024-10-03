// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleTypesTimestampImpl.dfy"
include "SimpleTimestampImplTest.dfy"

module WrappedSimpleTypesTimestampTest {
    import WrappedSimpleTypesTimestampService
    import SimpleTimestampImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpleTypesTimestampService.WrappedSimpleTimestamp();

        SimpleTimestampImplTest.TestGetTimestamp(client);
        SimpleTimestampImplTest.TestGetTimestampNoMs(client);
    }
}
