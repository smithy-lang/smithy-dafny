# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_dependencies_internaldafny
import simple_dependencies_internaldafny_wrapped
from simple_dependencies.smithygenerated.simple_dependencies.client import SimpleDependencies
from simple_dependencies.smithygenerated.simple_dependencies.config import dafny_config_to_smithy_config
from simple_dependencies.smithygenerated.simple_dependencies.shim import SimpleDependenciesShim
import standard_library.internaldafny.generated.Wrappers as Wrappers

@staticmethod
def WrappedSimpleDependencies(config):
    # Use an alternate internal-Dafny constructor to create the Dafny client, then pass that directly into the Smithy client
    dafny_client = simple_dependencies_internaldafny.default__.SimpleDependencies(config).value
    impl = SimpleDependencies(dafny_client=dafny_client)
    wrapped_client = SimpleDependenciesShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_dependencies_internaldafny_wrapped.default__.WrappedSimpleDependencies = WrappedSimpleDependencies
