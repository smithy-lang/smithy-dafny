// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module {:options "--function-syntax:4"} $sdkID:LImplTest {

    import $sdkID:L
    import opened $dafnyModuleName:LTypes
    import opened Wrappers

    method {:test} TestClient(){
        var client :- expect $sdkID:L.$sdkID:L();
        
        expect false, "...that you'll write actual tests using the client here :)";
        // TestSomeOperation1(client);
        // TestSomeOperation2(client);
        // ...
    }
}