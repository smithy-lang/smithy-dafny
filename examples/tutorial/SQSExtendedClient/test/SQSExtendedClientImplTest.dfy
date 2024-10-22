// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module {:options "--function-syntax:4"} SQSExtendedClientImplTest {

    import SQSExtended
    import opened PolymorphTutorialSqsextendedTypes
    import opened Wrappers

    method {:test} TestClient(){
        // var client :- expect SQSExtendedClient.SQSExtendedClient();

        expect false, "...that you'll write actual tests using the client here :)";
        // TestSomeOperation1(client);
        // TestSomeOperation2(client);
        // ...
    }
}
