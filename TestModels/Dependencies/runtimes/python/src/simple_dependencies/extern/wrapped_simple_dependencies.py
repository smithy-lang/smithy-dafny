# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_dependencies_internaldafny
import simple_dependencies_internaldafny_wrapped
from simple_dependencies.smithygenerated.client import SimpleDependencies
from simple_dependencies.smithygenerated.config import dafny_config_to_smithy_config
from simple_dependencies.smithygenerated.shim import SimpleDependenciesShim
import Wrappers

@staticmethod
def WrappedSimpleDependencies(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleDependencies(wrapped_config)
    # TODO: Generate an alternate constructor for Smithy client that does not take in a config,
    # but instead takes in an extern-supplied Dafny client
    # and also converts its Config to the Smithy config
    # SIM: https://sim.amazon.com/issues/CrypTool-5230
    impl._config.dafnyImplInterface.impl = simple_dependencies_internaldafny.default__.SimpleDependencies(config).value
    wrapped_client = SimpleDependenciesShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_dependencies_internaldafny_wrapped.default__.WrappedSimpleDependencies = WrappedSimpleDependencies
