# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_union.smithygenerated.simple_union.client import SimpleUnion
from simple_union.smithygenerated.simple_union.shim import SimpleUnionShim
from simple_union.smithygenerated.simple_union.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleUnionService

class default__(WrappedSimpleUnionService.default__):

    @staticmethod
    def WrappedSimpleUnion(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleUnion(wrapped_config)
        wrapped_client = SimpleUnionShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleUnionService.default__ = default__