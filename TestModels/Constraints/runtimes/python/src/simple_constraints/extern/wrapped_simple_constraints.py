# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_constraints_internaldafny_wrapped
from simple_constraints.smithygenerated.client import SimpleConstraints
from simple_constraints.smithygenerated.shim import SimpleConstraintsShim
import Wrappers

@staticmethod
def WrappedSimpleConstraints(config):
    wrapped_config = config
    impl = SimpleConstraints(wrapped_config)
    wrapped_client = SimpleConstraintsShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_constraints_internaldafny_wrapped.default__.WrappedSimpleConstraints = WrappedSimpleConstraints
