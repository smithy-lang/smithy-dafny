# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_smithyenum_internaldafny_wrapped
from simple_types_smithyenum.smithygenerated.client import SimpleTypesEnum
from simple_types_smithyenum.smithygenerated.shim import SimpleEnumShim
import Wrappers

@staticmethod
def WrappedSimpleEnum(config):
    wrapped_config = config
    impl = SimpleTypesEnum(wrapped_config)
    wrapped_client = SimpleEnumShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_smithyenum_internaldafny_wrapped.default__.WrappedSimpleEnum = WrappedSimpleEnum
