# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_smithydouble_internaldafny_wrapped
from simple_types_smithydouble.smithygenerated.client import SimpleTypesDouble
from simple_types_smithydouble.smithygenerated.shim import SimpleDoubleShim
import Wrappers

@staticmethod
def WrappedSimpleDouble(config):
    wrapped_config = config
    impl = SimpleTypesDouble(wrapped_config)
    wrapped_client = SimpleDoubleShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_smithydouble_internaldafny_wrapped.default__.WrappedSimpleDouble = WrappedSimpleDouble
