# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_smithylong.smithygenerated.simple_types_smithylong.client import SimpleTypesLong
from simple_types_smithylong.smithygenerated.simple_types_smithylong.shim import SimpleLongShim
from simple_types_smithylong.smithygenerated.simple_types_smithylong.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesLongService

class default__(WrappedSimpleTypesLongService.default__):

    @staticmethod
    def WrappedSimpleLong(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesLong(wrapped_config)
        wrapped_client = SimpleLongShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesLongService.default__ = default__