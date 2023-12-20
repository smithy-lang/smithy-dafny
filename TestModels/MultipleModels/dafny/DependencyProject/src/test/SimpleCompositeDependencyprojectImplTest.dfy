// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleMultiplemodelsDependencyprojectImplTest {
    import SimpleMultiplemodelsDependencyprojectService
    import opened SimpleMultiplemodelsDependencyprojectTypes
    import opened Wrappers
    method{:test} TestDependencyProject(){
        var client :- expect SimpleMultiplemodelsDependencyprojectService.DependencyProject();
    }
}