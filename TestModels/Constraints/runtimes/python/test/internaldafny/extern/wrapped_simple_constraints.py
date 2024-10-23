# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_constraints.smithygenerated.simple_constraints.client import SimpleConstraints
from simple_constraints.smithygenerated.simple_constraints.shim import SimpleConstraintsShim
from simple_constraints.smithygenerated.simple_constraints.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleConstraintsService

class default__(WrappedSimpleConstraintsService.default__):

    @staticmethod
    def WrappedSimpleConstraints(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleConstraints(wrapped_config)
        wrapped_client = SimpleConstraintsShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleConstraintsService.default__ = default__