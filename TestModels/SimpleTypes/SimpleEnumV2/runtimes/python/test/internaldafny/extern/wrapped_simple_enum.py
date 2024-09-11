# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_smithyenumv2.smithygenerated.simple_types_enumv2.client import SimpleTypesEnumV2
from simple_types_smithyenumv2.smithygenerated.simple_types_enumv2.shim import SimpleEnumV2Shim
from simple_types_smithyenumv2.smithygenerated.simple_types_enumv2.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesEnumV2Service

class default__(WrappedSimpleTypesEnumV2Service.default__):

    @staticmethod
    def WrappedSimpleEnumV2(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesEnumV2(wrapped_config)
        wrapped_client = SimpleEnumV2Shim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesEnumV2Service.default__ = default__