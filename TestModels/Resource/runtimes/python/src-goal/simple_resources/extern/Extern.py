# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.resources.internaldafny.wrapped
from simple_resources.smithy_generated.simple_resources.client import SimpleResources
from simple_resources.smithy_generated.simple_resources.shim import (
    SimpleResourcesShim,
)
from simple_resources.smithy_generated.simple_resources.config import (
    dafny_config_to_smithy_config
)
import Wrappers_Compile

@staticmethod
def WrappedSimpleResources(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    print("wrapped_config")
    print(wrapped_config)
    impl = SimpleResources(wrapped_config)
    wrapped_client = SimpleResourcesShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.resources.internaldafny.wrapped.default__.WrappedSimpleResources = WrappedSimpleResources
