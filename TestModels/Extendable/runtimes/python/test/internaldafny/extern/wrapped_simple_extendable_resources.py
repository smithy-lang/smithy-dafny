# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_extendable_resources_internaldafny_wrapped
from smithygenerated.simple_extendable_resources.client import SimpleExtendableResources
from smithygenerated.simple_extendable_resources.shim import SimpleExtendableResourcesShim
from smithygenerated.simple_extendable_resources.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_extendable_resources_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleExtendableResources(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleExtendableResources(wrapped_config)
        wrapped_client = SimpleExtendableResourcesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_extendable_resources_internaldafny_wrapped.default__ = default__
