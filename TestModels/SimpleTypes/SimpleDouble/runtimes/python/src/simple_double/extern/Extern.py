# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.smithydouble.internaldafny.wrapped
from simple_double.smithy_generated.simple_double.client import SimpleTypesDouble
from simple_double.smithy_generated.simple_double.shim import SimpleDoubleShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleDouble(config):
    wrapped_config = config
    impl = SimpleTypesDouble(wrapped_config)
    wrapped_client = SimpleDoubleShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.smithydouble.internaldafny.wrapped.default__.WrappedSimpleDouble = WrappedSimpleDouble
