# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.constraints.internaldafny.wrapped
from simple_constraints.smithy_generated.simple_constraints.client import SimpleConstraints
from simple_constraints.smithy_generated.simple_constraints.shim import SimpleConstraintsShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleConstraints(config):
    wrapped_config = config
    impl = SimpleConstraints(wrapped_config)
    wrapped_client = SimpleConstraintsShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.constraints.internaldafny.wrapped.default__.WrappedSimpleConstraints = WrappedSimpleConstraints
