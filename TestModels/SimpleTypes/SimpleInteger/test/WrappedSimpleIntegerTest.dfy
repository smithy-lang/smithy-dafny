// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleIntegerImpl.dfy"
include "SimpleIntegerImplTest.dfy"

module WrappedSimpleTypesIntegerTest {
    import WrappedSimpleTypesIntegerService
    import SimpleIntegerImplTest
    import opened Wrappers
    method{:test} GetInteger() {
        var client :- expect WrappedSimpleTypesIntegerService.WrappedSimpleInteger();
        SimpleIntegerImplTest.TestGetInteger(client);
        SimpleIntegerImplTest.TestGetIntegerKnownValue(client);
        SimpleIntegerImplTest.TestGetIntegerEdgeCases(client);
    }
}