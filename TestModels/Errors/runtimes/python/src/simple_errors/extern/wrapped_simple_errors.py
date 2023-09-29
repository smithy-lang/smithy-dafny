# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_errors_internaldafny_wrapped
from simple_errors.smithygenerated.config import dafny_config_to_smithy_config
from simple_errors.smithygenerated.client import SimpleErrors
from simple_errors.smithygenerated.shim import SimpleErrorsShim
import Wrappers

@staticmethod
def WrappedSimpleErrors(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleErrors(wrapped_config)
    wrapped_client = SimpleErrorsShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_errors_internaldafny_wrapped.default__.WrappedSimpleErrors = WrappedSimpleErrors
