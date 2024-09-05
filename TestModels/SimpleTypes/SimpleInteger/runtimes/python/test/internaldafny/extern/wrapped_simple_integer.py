# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier:er

# src imports
from simple_types_integer.smithygenerated.simple_types_integer.client import SimpleTypesInteger
from simple_types_integer.smithygenerated.simple_types_integer.shim import SimpleIntegerShim
from simple_types_integer.smithygenerated.simple_types_integer.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesIntegerService

class default__(WrappedSimpleTypesIntegerService.default__):

    @staticmethod
    def WrappedSimpleInteger(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesInteger(wrapped_config)
        wrapped_client = SimpleIntegerShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesIntegerService.default__ = default__