// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCodegenpatchesTypesWrapped.dfy"

module {:extern "simple.codegenpatches.internaldafny.wrapped"} WrappedSimpleCodegenPatchesService refines WrappedAbstractSimpleCodegenpatchesService {
    import WrappedService = CodegenPatches
    function method WrappedDefaultCodegenPatchesConfig(): CodegenPatchesConfig {
        CodegenPatchesConfig
    }
}
