# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_dependencies_internaldafny_wrapped
from simple_dependencies.smithygenerated.client import SimpleDependencies
from simple_dependencies.smithygenerated.config import dafny_config_to_smithy_config
from simple_dependencies.smithygenerated.shim import SimpleDependenciesShim
import Wrappers

@staticmethod
def WrappedSimpleDependencies(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    print("wrapped_config")
    print(wrapped_config)
    print(wrapped_config.__dict__)
    print(config)
    impl = SimpleDependencies(wrapped_config)
    wrapped_client = SimpleDependenciesShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_dependencies_internaldafny_wrapped.default__.WrappedSimpleDependencies = WrappedSimpleDependencies
