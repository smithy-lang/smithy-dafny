// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsPrimaryprojectTypesWrapped.dfy"

module {:extern "simple.multiplemodels.primaryproject.internaldafny.wrapped"} WrappedSimpleMultiplemodelsPrimaryprojectService refines WrappedAbstractSimpleMultiplemodelsPrimaryprojectService {
    import WrappedService = PrimaryProject
    function method WrappedDefaultPrimaryProjectConfig(): PrimaryProjectConfig {
        PrimaryProjectConfig
    }
}
