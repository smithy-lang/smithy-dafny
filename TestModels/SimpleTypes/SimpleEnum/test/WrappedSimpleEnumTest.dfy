// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleEnumImpl.dfy"
include "SimpleEnumImplTest.dfy"

module WrappedSimpleTypesEnumTest {
    import WrappedSimpleTypesSmithyEnumService
    import SimpleEnumImplTest
    import opened Wrappers
    method{:test} GetEnum() {
        var client :- expect WrappedSimpleTypesSmithyEnumService.WrappedSimpleEnum();
        SimpleEnumImplTest.TestGetEnum(client);
        SimpleEnumImplTest.TestGetEnumFirstKnownValueTest(client);
        SimpleEnumImplTest.TestGetEnumSecondKnownValueTest(client);
        SimpleEnumImplTest.TestGetEnumThirdKnownValueTest(client);
    }
}