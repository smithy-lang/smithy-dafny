# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.smithylong.internaldafny.wrapped
from simple_long.smithy_generated.simple_long.client import SimpleTypesLong
from simple_long.smithy_generated.simple_long.shim import SimpleLongShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleLong(config):
    wrapped_config = config
    impl = SimpleTypesLong(wrapped_config)
    wrapped_client = SimpleLongShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.smithylong.internaldafny.wrapped.default__.WrappedSimpleLong = WrappedSimpleLong
