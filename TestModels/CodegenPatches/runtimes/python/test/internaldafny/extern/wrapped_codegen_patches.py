# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from codegen_patches.smithygenerated.simple_codegenpatches.client import CodegenPatches
from codegen_patches.smithygenerated.simple_codegenpatches.shim import CodegenPatchesShim
from codegen_patches.smithygenerated.simple_codegenpatches.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleCodegenPatchesService

class default__(WrappedSimpleCodegenPatchesService.default__):

    @staticmethod
    def WrappedCodegenPatches(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = CodegenPatches(wrapped_config)
        wrapped_client = CodegenPatchesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleCodegenPatchesService.default__ = default__