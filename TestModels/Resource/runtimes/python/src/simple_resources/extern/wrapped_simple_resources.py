# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_resources_internaldafny_wrapped
from simple_resources.smithygenerated.client import SimpleResources
from simple_resources.smithygenerated.shim import SimpleResourcesShim
import Wrappers

@staticmethod
def WrappedSimpleResources(config):
    wrapped_config = config
    impl = SimpleResources(wrapped_config)
    wrapped_client = SimpleResourcesShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_resources_internaldafny_wrapped.default__.WrappedSimpleResources = WrappedSimpleResources
