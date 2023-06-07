// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleLongImpl.dfy"
include "SimpleLongImplTest.dfy"

module WrappedSimpleTypesLongTest {
    import WrappedSimpleTypesLongService
    import SimpleLongImplTest
    import opened Wrappers
    method{:test} GetLong() {
        var client :- expect WrappedSimpleTypesLongService.WrappedSimpleLong();
        SimpleLongImplTest.TestGetLong(client);
        SimpleLongImplTest.TestGetLongEdgeCases(client);
        SimpleLongImplTest.TestGetLongKnownValueTest(client);
    }
}