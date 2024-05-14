# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_constructor_internaldafny_wrapped
from simple_constructor.smithygenerated.simple_constructor.client import SimpleConstructor
from simple_constructor.smithygenerated.simple_constructor.shim import SimpleConstructorShim
from simple_constructor.smithygenerated.simple_constructor.config import dafny_config_to_smithy_config
import standard_library.internaldafny.generated.Wrappers as Wrappers

class default__(simple_constructor_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleConstructor(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleConstructor(wrapped_config)
        wrapped_client = SimpleConstructorShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_constructor_internaldafny_wrapped.default__ = default__
