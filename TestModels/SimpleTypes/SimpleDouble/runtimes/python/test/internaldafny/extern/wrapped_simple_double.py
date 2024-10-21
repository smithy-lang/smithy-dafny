# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.client import SimpleTypesDouble
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.shim import SimpleDoubleShim
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesDouble

class default__(WrappedSimpleTypesDouble.default__):

    @staticmethod
    def WrappedSimpleDouble(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesDouble(wrapped_config)
        wrapped_client = SimpleDoubleShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesDouble.default__ = default__