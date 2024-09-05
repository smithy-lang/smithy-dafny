# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_localservice.smithygenerated.simple_localservice.client import SimpleLocalService
from simple_localservice.smithygenerated.simple_localservice.shim import SimpleLocalServiceShim
from simple_localservice.smithygenerated.simple_localservice.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleLocalService

class default__(WrappedSimpleLocalService.default__):

    @staticmethod
    def WrappedSimpleLocalService(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleLocalService(wrapped_config)
        wrapped_client = SimpleLocalServiceShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleLocalService.default__ = default__