# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_smithylong_internaldafny_wrapped
from simple_types_smithylong.smithygenerated.config import dafny_config_to_smithy_config
from simple_types_smithylong.smithygenerated.client import SimpleTypesLong
from simple_types_smithylong.smithygenerated.shim import SimpleLongShim
import Wrappers

@staticmethod
def WrappedSimpleLong(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleTypesLong(wrapped_config)
    wrapped_client = SimpleLongShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_smithylong_internaldafny_wrapped.default__.WrappedSimpleLong = WrappedSimpleLong
