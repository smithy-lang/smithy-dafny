# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.integer.internaldafny.wrapped
from simple_integer.smithy_generated.simple_integer.client import SimpleTypesInteger
from simple_integer.smithy_generated.simple_integer.shim import SimpleIntegerShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleInteger(config):
    wrapped_config = config
    impl = SimpleTypesInteger(wrapped_config)
    wrapped_client = SimpleIntegerShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.integer.internaldafny.wrapped.default__.WrappedSimpleInteger = WrappedSimpleInteger
