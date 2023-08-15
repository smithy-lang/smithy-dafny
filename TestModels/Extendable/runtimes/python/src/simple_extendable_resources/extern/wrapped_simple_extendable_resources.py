# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_extendable_resources_internaldafny_wrapped
from simple_extendable_resources.smithygenerated.client import SimpleExtendableResources
from simple_extendable_resources.smithygenerated.shim import SimpleExtendableResourcesShim
import Wrappers

@staticmethod
def WrappedSimpleExtendableResources(config):
    wrapped_config = config
    impl = SimpleExtendableResources(wrapped_config)
    wrapped_client = SimpleExtendableResourcesShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_extendable_resources_internaldafny_wrapped.default__.WrappedSimpleExtendableResources = WrappedSimpleExtendableResources
