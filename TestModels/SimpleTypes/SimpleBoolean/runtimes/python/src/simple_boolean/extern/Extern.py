# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.boolean.internaldafny.wrapped
from simple_boolean.smithy_generated.simple_boolean.client import SimpleTypesBoolean
from .Shim import SimpleBooleanShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleTypesBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean
