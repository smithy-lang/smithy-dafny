// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsDependencyprojectTypesWrapped.dfy"

module {:extern "simple.multiplemodels.dependencyproject.internaldafny.wrapped"} WrappedSimpleMultiplemodelsDependencyprojectService refines WrappedAbstractSimpleMultiplemodelsDependencyprojectService {
    import WrappedService = DependencyProject
    function method WrappedDefaultDependencyProjectConfig(): DependencyProjectConfig {
        DependencyProjectConfig
    }
}
