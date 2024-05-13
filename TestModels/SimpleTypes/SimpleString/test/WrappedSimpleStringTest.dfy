// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleStringImpl.dfy"
include "SimpleStringImplTest.dfy"

module WrappedSimpleTypesStringTest {
    import WrappedSimpleTypesStringService
    import SimpleStringImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpleTypesStringService.WrappedSimpleString();
        SimpleStringImplTest.TestGetString(client);
        SimpleStringImplTest.TestGetStringKnownValue(client);
        SimpleStringImplTest. TestGetStringUTF8(client);
    }
}
