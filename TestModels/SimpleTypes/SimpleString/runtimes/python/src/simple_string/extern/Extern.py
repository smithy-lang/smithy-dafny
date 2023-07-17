# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.smithystring.internaldafny.wrapped
from simple_string.smithy_generated.simple_string.client import SimpleTypesString
from simple_string.smithy_generated.simple_string.shim import SimpleStringShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleString(config):
    wrapped_config = config
    impl = SimpleTypesString(wrapped_config)
    wrapped_client = SimpleStringShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.smithystring.internaldafny.wrapped.default__.WrappedSimpleString = WrappedSimpleString
