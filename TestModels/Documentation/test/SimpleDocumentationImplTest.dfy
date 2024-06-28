// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module {:options "--function-syntax:4"} SimpleDocumentationImplTest {

    import SimpleDocumentation
    import opened SimpleDocumentationTypes
    import opened Wrappers

    method {:test} TestClient(){
        var client :- expect SimpleDocumentation.SimpleDocumentation();

        // We're only testing that the code compiles and runs this far,
        // since the point of the test model is generating documentation
        // which needs manual inspection.
    }
}
