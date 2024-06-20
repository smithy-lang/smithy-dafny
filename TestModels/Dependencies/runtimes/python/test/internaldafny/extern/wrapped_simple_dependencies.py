# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_dependencies.smithygenerated.simple_dependencies.client import SimpleDependencies
from simple_dependencies.smithygenerated.simple_dependencies.shim import SimpleDependenciesShim
from simple_dependencies.smithygenerated.simple_dependencies.config import dafny_config_to_smithy_config
import standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleDependencies

class default__(WrappedSimpleDependencies.default__):

    @staticmethod
    def WrappedSimpleDependencies(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleDependencies(wrapped_config)
        wrapped_client = SimpleDependenciesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleDependencies.default__ = default__