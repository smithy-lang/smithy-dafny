# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_smithystring.smithygenerated.simple_types_smithystring.client import SimpleTypesString
from simple_types_smithystring.smithygenerated.simple_types_smithystring.shim import SimpleStringShim
from simple_types_smithystring.smithygenerated.simple_types_smithystring.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesStringService

class default__(WrappedSimpleTypesStringService.default__):

    @staticmethod
    def WrappedSimpleString(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesString(wrapped_config)
        wrapped_client = SimpleStringShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesStringService.default__ = default__