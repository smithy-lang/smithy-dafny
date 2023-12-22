// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsPrimaryprojectTypesWrapped.dfy"

module {:extern "simple.multiplemodels.primaryproject.internaldafny.wrapped"} WrappedSimpleMultiplemodelsPrimaryprojectService refines WrappedAbstractSimpleMultiplemodelsPrimaryprojectService {
    import WrappedService = SimpleMultiplemodelsPrimaryprojectService
    function method WrappedDefaultPrimaryProjectConfig(): PrimaryProjectConfig {
        PrimaryProjectConfig
    }
}
