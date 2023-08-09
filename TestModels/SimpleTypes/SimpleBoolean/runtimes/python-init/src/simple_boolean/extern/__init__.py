# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import standard_library

import sys
print(sys.modules)
from simple_boolean.smithy.client import SimpleTypesBoolean
from simple_boolean.smithy.shim import SimpleBooleanShim
import Wrappers

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleTypesBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers.Result_Success(wrapped_client)

try:
    simple_types_boolean_internaldafny_wrapped = sys.modules["simple_types_boolean_internaldafny_wrapped"]
except KeyError:
    import types
    simple_types_boolean_internaldafny_wrapped = types.ModuleType("simple_types_boolean_internaldafny_wrapped")
# setattr(simple_types_boolean_internaldafny_wrapped, 'default__', types.ModuleType("default__"))
# setattr(simple_types_boolean_internaldafny_wrapped.default__, 'WrappedSimpleBoolean', WrappedSimpleBoolean)
simple_types_boolean_internaldafny_wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean
sys.modules["simple_types_boolean_internaldafny_wrapped"] = simple_types_boolean_internaldafny_wrapped