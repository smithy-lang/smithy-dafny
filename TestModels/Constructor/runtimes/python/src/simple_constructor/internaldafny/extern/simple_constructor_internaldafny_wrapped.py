# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_constructor_internaldafny_wrapped
from smithygenerated.simple_constructor.client import SimpleConstructor
from smithygenerated.simple_constructor.shim import SimpleConstructorShim
from smithygenerated.simple_constructor.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_constructor_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleConstructor(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleConstructor(wrapped_config)
        wrapped_client = SimpleConstructorShim(impl)
        return Wrappers.Result_Success(wrapped_client)

simple_constructor_internaldafny_wrapped.default__ = default__