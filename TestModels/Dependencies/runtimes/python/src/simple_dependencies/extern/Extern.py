# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.dependencies.internaldafny.wrapped
from simple_dependencies.smithy_generated.simple_dependencies.client import SimpleDependencies
from simple_dependencies.smithy_generated.simple_dependencies.shim import SimpleDependenciesShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleDependencies(config):
    wrapped_config = config
    impl = SimpleDependencies(wrapped_config)
    wrapped_client = SimpleDependenciesShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.dependencies.internaldafny.wrapped.default__.WrappedSimpleDependencies = WrappedSimpleDependencies
