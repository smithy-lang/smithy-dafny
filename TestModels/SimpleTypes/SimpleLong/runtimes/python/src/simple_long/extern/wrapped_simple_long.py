# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_smithylong_internaldafny_wrapped
from simple_long.smithygenerated.client import SimpleTypesLong
from simple_long.smithygenerated.shim import SimpleLongShim
import Wrappers

@staticmethod
def WrappedSimpleLong(config):
    wrapped_config = config
    impl = SimpleTypesLong(wrapped_config)
    wrapped_client = SimpleLongShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_smithylong_internaldafny_wrapped.default__.WrappedSimpleLong = WrappedSimpleLong
