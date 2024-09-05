# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_constructor.smithygenerated.simple_constructor.client import SimpleConstructor
from simple_constructor.smithygenerated.simple_constructor.shim import SimpleConstructorShim
from simple_constructor.smithygenerated.simple_constructor.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleConstructorService

class default__(WrappedSimpleConstructorService.default__):

    @staticmethod
    def WrappedSimpleConstructor(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleConstructor(wrapped_config)
        wrapped_client = SimpleConstructorShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleConstructorService.default__ = default__