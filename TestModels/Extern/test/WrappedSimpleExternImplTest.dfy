// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleExternImpl.dfy"
include "SimpleExternImplTest.dfy"

module WrappedSimpleExternTest {
    import WrappedSimpleExternService
    import opened SimpleDafnyExternTypes
    import SimpleExternImplTest
    import opened Wrappers
    
    method{:test} Externs() {
        var client :- expect WrappedSimpleExternService.WrappedSimpleExtern();
        SimpleExternImplTest.TestGetExtern(client);
        SimpleExternImplTest.TestExternMustError(client);
        SimpleExternImplTest.TestUseClassExternSuccess(client);
        SimpleExternImplTest.TestUseClassExternFailure(client);
    }
}
