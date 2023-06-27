# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.errors.internaldafny.wrapped
from simple_errors.smithy_generated.simple_errors.client import SimpleErrors
from simple_errors.smithy_generated.simple_errors.shim import SimpleErrorsShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleErrors(config):
    wrapped_config = config
    impl = SimpleErrors(wrapped_config)
    wrapped_client = SimpleErrorsShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.errors.internaldafny.wrapped.default__.WrappedSimpleErrors = WrappedSimpleErrors
