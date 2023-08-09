# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import sys
# import simple.types.boolean.internaldafny.wrapped
from simple_boolean.client import SimpleTypesBoolean
from simple_boolean.shim import SimpleBooleanShim
from simple_boolean import Wrappers

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleTypesBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers.Result_Success(wrapped_client)

try:
    simple_types_boolean_internaldafny_wrapped = sys.modules["simple_types_boolean_internaldafny_wrapped"]
except KeyError:
    simple_types_boolean_internaldafny_wrapped = oops()
    sys.modules["simple_types_boolean_internaldafny_wrapped"] = simple_types_boolean_internaldafny_wrapped
simple_types_boolean_internaldafny_wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean
sys.modules["simple_types_boolean_internaldafny_wrapped"] = simple_types_boolean_internaldafny_wrapped