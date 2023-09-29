# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_smithystring_internaldafny_wrapped
from simple_types_smithystring.smithygenerated.config import dafny_config_to_smithy_config
from simple_types_smithystring.smithygenerated.client import SimpleTypesString
from simple_types_smithystring.smithygenerated.shim import SimpleStringShim
import Wrappers

@staticmethod
def WrappedSimpleString(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleTypesString(wrapped_config)
    wrapped_client = SimpleStringShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_smithystring_internaldafny_wrapped.default__.WrappedSimpleString = WrappedSimpleString
