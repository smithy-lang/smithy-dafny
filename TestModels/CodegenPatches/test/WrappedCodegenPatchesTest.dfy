// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedCodegenPatchesImpl.dfy"
include "CodegenPatchesImplTest.dfy"

//TODO: This will not compile in Go because https://t.corp.amazon.com/P153280434
module WrappedCodegenPatchesTest {
    import WrappedSimpleCodegenPatchesService
    import CodegenPatchesImplTest
    import opened Wrappers
    method{:test} GetString() {
        var client :- expect WrappedSimpleCodegenPatchesService.WrappedCodegenPatches();
        CodegenPatchesImplTest.TestGetString(client);
    }
}