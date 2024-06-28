// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleDocumentationImpl.dfy"
include "SimpleDocumentationImplTest.dfy"

module WrappedSimpleDocumentationTest {
    import WrappedSimpleDocumentationService
    import SimpleDocumentationImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpleDocumentationService.WrappedSimpleDocumentation();

        // We're only testing that the code compiles and runs this far,
        // since the point of the test model is generating documentation
        // which needs manual inspection.
    }
}
