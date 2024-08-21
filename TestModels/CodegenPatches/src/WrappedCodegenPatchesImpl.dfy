// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCodegenpatchesTypesWrapped.dfy"

module WrappedSimpleCodegenpatchesService refines WrappedAbstractSimpleCodegenpatchesService {
    import WrappedService = CodegenPatches
    function method WrappedDefaultCodegenPatchesConfig(): CodegenPatchesConfig {
        CodegenPatchesConfig
    }
}
