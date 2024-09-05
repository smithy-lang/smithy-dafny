# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_resources.smithygenerated.simple_resources.client import SimpleResources
from simple_resources.smithygenerated.simple_resources.shim import SimpleResourcesShim
from simple_resources.smithygenerated.simple_resources.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleResources

class default__(WrappedSimpleResources.default__):

    @staticmethod
    def WrappedSimpleResources(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleResources(wrapped_config)
        wrapped_client = SimpleResourcesShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleResources.default__ = default__