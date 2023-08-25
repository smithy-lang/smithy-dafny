# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_dafnyextern_internaldafny_wrapped
from simple_dafnyextern.smithygenerated.client import SimpleExtern
from simple_dafnyextern.smithygenerated.config import dafny_config_to_smithy_config
from simple_dafnyextern.smithygenerated.shim import SimpleExternShim
import Wrappers

@staticmethod
def WrappedSimpleExtern(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleExtern(wrapped_config)
    wrapped_client = SimpleExternShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_dafnyextern_internaldafny_wrapped.default__.WrappedSimpleExtern = WrappedSimpleExtern
