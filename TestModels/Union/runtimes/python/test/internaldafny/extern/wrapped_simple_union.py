# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_union_internaldafny_wrapped
from simple_union.smithygenerated.simple_union.client import SimpleUnion
from simple_union.smithygenerated.simple_union.shim import SimpleUnionShim
from simple_union.smithygenerated.simple_union.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_union_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleUnion(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleUnion(wrapped_config)
        wrapped_client = SimpleUnionShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_union_internaldafny_wrapped.default__ = default__
