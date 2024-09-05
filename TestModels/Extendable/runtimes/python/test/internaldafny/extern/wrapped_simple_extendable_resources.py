# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_extendable_resources.smithygenerated.simple_extendable_resources.client import SimpleExtendableResources
from simple_extendable_resources.smithygenerated.simple_extendable_resources.shim import SimpleExtendableResourcesShim
from simple_extendable_resources.smithygenerated.simple_extendable_resources.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleExtendableResources

class default__(WrappedSimpleExtendableResources.default__):

    @staticmethod
    def WrappedSimpleExtendableResources(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleExtendableResources(wrapped_config)
        wrapped_client = SimpleExtendableResourcesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleExtendableResources.default__ = default__