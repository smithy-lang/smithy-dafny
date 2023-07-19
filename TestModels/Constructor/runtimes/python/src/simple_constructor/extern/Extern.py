# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.constructor.internaldafny.wrapped
from simple_constructor.smithy_generated.simple_constructor.client import SimpleConstructor
from simple_constructor.smithy_generated.simple_constructor.shim import (
    SimpleConstructorShim,
)
from simple_constructor.smithy_generated.simple_constructor.config import (
    dafny_config_to_smithy_config
)
import Wrappers_Compile

@staticmethod
def WrappedSimpleConstructor(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    print("wrapped_config")
    print(wrapped_config)
    impl = SimpleConstructor(wrapped_config)
    wrapped_client = SimpleConstructorShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.constructor.internaldafny.wrapped.default__.WrappedSimpleConstructor = WrappedSimpleConstructor
