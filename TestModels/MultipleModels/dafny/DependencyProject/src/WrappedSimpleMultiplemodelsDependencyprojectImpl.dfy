// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsDependencyprojectTypesWrapped.dfy"

module WrappedSimpleMultiplemodelsDependencyprojectService refines WrappedAbstractSimpleMultiplemodelsDependencyprojectService {
    import WrappedService = DependencyProject
    function method WrappedDefaultDependencyProjectConfig(): DependencyProjectConfig {
        DependencyProjectConfig
    }
}
