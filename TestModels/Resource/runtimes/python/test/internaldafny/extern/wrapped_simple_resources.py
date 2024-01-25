# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_resources_internaldafny_wrapped
from simple_resources.smithygenerated.simple_resources.client import SimpleResources
from simple_resources.smithygenerated.simple_resources.shim import SimpleResourcesShim
from simple_resources.smithygenerated.simple_resources.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_resources_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleResources(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleResources(wrapped_config)
        wrapped_client = SimpleResourcesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_resources_internaldafny_wrapped.default__ = default__
