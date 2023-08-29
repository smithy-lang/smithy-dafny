# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_union_internaldafny_wrapped
from simple_union.smithygenerated.client import SimpleUnion
from simple_union.smithygenerated.config import dafny_config_to_smithy_config
from simple_union.smithygenerated.shim import SimpleUnionShim
import Wrappers

@staticmethod
def WrappedSimpleUnion(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleUnion(wrapped_config)
    wrapped_client = SimpleUnionShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_union_internaldafny_wrapped.default__.WrappedSimpleUnion = WrappedSimpleUnion
