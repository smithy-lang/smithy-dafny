// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleErrorsImpl.dfy"
include "SimpleErrorsImplTest.dfy"

module WrappedSimpleErrorsTest {
    import WrappedSimpleErrorsService
    import SimpleErrorsImplTest
    import opened Wrappers
    method{:test} GetErrors() {
        var client :- expect WrappedSimpleErrorsService.WrappedSimpleErrors();
        SimpleErrorsImplTest.TestAlwaysError(client);
        SimpleErrorsImplTest.TestAlwaysMultipleErrors(client);
        SimpleErrorsImplTest.TestAlwaysNativeError(client);
    }
}