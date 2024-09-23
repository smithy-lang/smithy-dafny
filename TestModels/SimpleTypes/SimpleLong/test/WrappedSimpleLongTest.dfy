// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleLongImpl.dfy"
include "SimpleLongImplTest.dfy"

module WrappedSimpleTypesLongTest {
    import WrappedSimpleTypesSmithyLongService
    import SimpleLongImplTest
    import opened Wrappers
    method{:test} GetLong() {
        var client :- expect WrappedSimpleTypesSmithyLongService.WrappedSimpleLong();
        SimpleLongImplTest.TestGetLong(client);
        SimpleLongImplTest.TestGetLongEdgeCases(client);
        SimpleLongImplTest.TestGetLongKnownValueTest(client);
    }
}