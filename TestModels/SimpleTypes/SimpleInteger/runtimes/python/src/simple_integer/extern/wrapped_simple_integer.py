# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_integer_internaldafny_wrapped
from simple_integer.smithygenerated.client import SimpleTypesInteger
from simple_integer.smithygenerated.shim import SimpleIntegerShim
import Wrappers

@staticmethod
def WrappedSimpleInteger(config):
    wrapped_config = config
    impl = SimpleTypesInteger(wrapped_config)
    wrapped_client = SimpleIntegerShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_integer_internaldafny_wrapped.default__.WrappedSimpleInteger = WrappedSimpleInteger
