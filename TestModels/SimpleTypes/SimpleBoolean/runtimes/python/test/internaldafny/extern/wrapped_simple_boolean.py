# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports 
from simple_types_boolean.smithygenerated.simple_types_boolean.client import SimpleTypesBoolean
from simple_types_boolean.smithygenerated.simple_types_boolean.shim import SimpleBooleanShim
from simple_types_boolean.smithygenerated.simple_types_boolean.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesBooleanService

class default__(WrappedSimpleTypesBooleanService.default__):

    @staticmethod
    def WrappedSimpleBoolean(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesBoolean(wrapped_config)
        wrapped_client = SimpleBooleanShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesBooleanService.default__ = default__
