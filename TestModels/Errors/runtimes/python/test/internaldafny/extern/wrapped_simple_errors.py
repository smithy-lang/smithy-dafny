# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_errors_internaldafny_wrapped
from simple_errors.smithygenerated.simple_errors.client import SimpleErrors
from simple_errors.smithygenerated.simple_errors.shim import SimpleErrorsShim
from simple_errors.smithygenerated.simple_errors.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_errors_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleErrors(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleErrors(wrapped_config)
        wrapped_client = SimpleErrorsShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_errors_internaldafny_wrapped.default__ = default__
