// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsPrimaryprojectTypesWrapped.dfy"

module WrappedSimpleMultiplemodelsPrimaryprojectService refines WrappedAbstractSimpleMultiplemodelsPrimaryprojectService {
    import WrappedService = PrimaryProject
    function method WrappedDefaultPrimaryProjectConfig(): PrimaryProjectConfig {
        PrimaryProjectConfig
    }
}
