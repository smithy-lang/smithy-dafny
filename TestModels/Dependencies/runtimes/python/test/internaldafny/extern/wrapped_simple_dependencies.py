# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_dependencies.smithygenerated.simple_dependencies.client import SimpleDependencies
from simple_dependencies.smithygenerated.simple_dependencies.shim import SimpleDependenciesShim
from simple_dependencies.smithygenerated.simple_dependencies.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers
import simple_dependencies.internaldafny.generated.SimpleDependencies as DafnySimpleDependencies

# test imports, not qualified since this isn't in a package
import WrappedSimpleDependenciesService

class default__(WrappedSimpleDependenciesService.default__):

    @staticmethod
    def WrappedSimpleDependencies(config):
        # Use an alternate internal-Dafny constructor to create the Dafny client, then pass that directly into the Smithy client
        dafny_client = DafnySimpleDependencies.default__.SimpleDependencies(config).value
        impl = SimpleDependencies(dafny_client=dafny_client)
        wrapped_client = SimpleDependenciesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleDependenciesService.default__ = default__