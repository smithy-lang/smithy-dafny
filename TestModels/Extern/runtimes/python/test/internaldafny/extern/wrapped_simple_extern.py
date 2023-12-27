# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_dafnyextern_internaldafny_wrapped
from simple_dafnyextern.smithygenerated.simple_dafnyextern.client import SimpleExtern
from simple_dafnyextern.smithygenerated.simple_dafnyextern.shim import SimpleExternShim
from simple_dafnyextern.smithygenerated.simple_dafnyextern.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_dafnyextern_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleExtern(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleExtern(wrapped_config)
        wrapped_client = SimpleExternShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_dafnyextern_internaldafny_wrapped.default__ = default__
