# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_dafnyextern.smithygenerated.simple_dafnyextern.client import SimpleExtern
from simple_dafnyextern.smithygenerated.simple_dafnyextern.shim import SimpleExternShim
from simple_dafnyextern.smithygenerated.simple_dafnyextern.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleExternService

class default__(WrappedSimpleExternService.default__):

    @staticmethod
    def WrappedSimpleExtern(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleExtern(wrapped_config)
        wrapped_client = SimpleExternShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleExternService.default__ = default__