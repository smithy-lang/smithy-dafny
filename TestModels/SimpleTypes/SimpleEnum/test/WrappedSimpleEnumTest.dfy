// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleEnumImpl.dfy"
include "SimpleEnumImplTest.dfy"

module WrappedSimpleTypesEnumTest {
    import WrappedSimpleTypesEnumService
    import SimpleEnumImplTest
    import opened Wrappers
    method{:test} GetEnum() {
        var client :- expect WrappedSimpleTypesEnumService.WrappedSimpleEnum();
        SimpleEnumImplTest.TestGetEnum(client);
        SimpleEnumImplTest.TestGetEnumFirstKnownValueTest(client);
        SimpleEnumImplTest.TestGetEnumSecondKnownValueTest(client);
        SimpleEnumImplTest.TestGetEnumThirdKnownValueTest(client);
    }
}