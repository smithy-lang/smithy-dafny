// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Wrapped$service:LImpl.dfy"
include "$sdkID:LImplTest.dfy"

module Wrapped$service:LTest {
    import Wrapped$service:LService
    import $sdkID:LImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect Wrapped$service:LService.Wrapped$sdkID:L();
        
        expect false, "...that you'll run the impl tests against the wrapped client";
        // $sdkID:LImplTest.TestSomeOperation1(client);
        // $sdkID:LImplTest.TestSomeOperation2(client);
        // ...
    }
}
