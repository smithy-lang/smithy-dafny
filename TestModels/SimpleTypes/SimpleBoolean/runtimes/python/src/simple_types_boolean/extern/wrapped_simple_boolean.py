# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from simple_types_boolean.smithygenerated.client import SimpleTypesBoolean
from simple_types_boolean.smithygenerated.shim import SimpleBooleanShim
import Wrappers
import simple_types_boolean_internaldafny_wrapped

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleTypesBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_boolean_internaldafny_wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean