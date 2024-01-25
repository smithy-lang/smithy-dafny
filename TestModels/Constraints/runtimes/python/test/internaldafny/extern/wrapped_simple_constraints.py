# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_constraints_internaldafny_wrapped
from simple_constraints.smithygenerated.simple_constraints.client import SimpleConstraints
from simple_constraints.smithygenerated.simple_constraints.shim import SimpleConstraintsShim
from simple_constraints.smithygenerated.simple_constraints.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_constraints_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleConstraints(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleConstraints(wrapped_config)
        wrapped_client = SimpleConstraintsShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_constraints_internaldafny_wrapped.default__ = default__
