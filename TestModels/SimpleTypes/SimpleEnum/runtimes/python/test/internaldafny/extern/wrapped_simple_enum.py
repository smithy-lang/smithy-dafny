# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_smithyenum.smithygenerated.simple_types_smithyenum.client import SimpleTypesEnum
from simple_types_smithyenum.smithygenerated.simple_types_smithyenum.shim import SimpleEnumShim
from simple_types_smithyenum.smithygenerated.simple_types_smithyenum.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesEnumService

class default__(WrappedSimpleTypesEnumService.default__):

    @staticmethod
    def WrappedSimpleEnum(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesEnum(wrapped_config)
        wrapped_client = SimpleEnumShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesEnumService.default__ = default__