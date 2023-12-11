// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleExternV2Impl.dfy"
include "SimpleExternV2ImplTest.dfy"

module WrappedSimpleExternV2Test {
    import WrappedSimpleExternV2Service
    import opened SimpleDafnyExternV2Types
    import SimpleExternV2ImplTest
    import opened Wrappers
    
    method{:test} ExternV2Tests() {
        var client :- expect WrappedSimpleExternV2Service.WrappedSimpleExternV2();
        SimpleExternV2ImplTest.TestGetExternV2(client);
        SimpleExternV2ImplTest.TestExternV2MustError(client);
        SimpleExternV2ImplTest.TestUseClassExternV2Success(client);
        SimpleExternV2ImplTest.TestUseClassExternV2Failure(client);
    }
}
