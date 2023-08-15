# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_constructor_internaldafny_wrapped
from simple_constructor.smithygenerated.client import SimpleConstructor
from simple_constructor.smithygenerated.shim import SimpleConstructorShim
import Wrappers

@staticmethod
def WrappedSimpleConstructor(config):
    wrapped_config = config
    impl = SimpleConstructor(wrapped_config)
    wrapped_client = SimpleConstructorShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_constructor_internaldafny_wrapped.default__.WrappedSimpleConstructor = WrappedSimpleConstructor
