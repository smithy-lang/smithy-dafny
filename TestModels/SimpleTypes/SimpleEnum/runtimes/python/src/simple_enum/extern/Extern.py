# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.smithyenum.internaldafny.wrapped
from simple_enum.smithy_generated.simple_enum.client import SimpleTypesEnum
from simple_enum.smithy_generated.simple_enum.shim import SimpleEnumShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleEnum(config):
    wrapped_config = config
    impl = SimpleTypesEnum(wrapped_config)
    wrapped_client = SimpleEnumShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.smithyenum.internaldafny.wrapped.default__.WrappedSimpleEnum = WrappedSimpleEnum
