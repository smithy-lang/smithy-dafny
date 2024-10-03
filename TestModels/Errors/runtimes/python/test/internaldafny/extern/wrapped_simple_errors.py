# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_errors.smithygenerated.simple_errors.client import SimpleErrors
from simple_errors.smithygenerated.simple_errors.shim import SimpleErrorsShim
from simple_errors.smithygenerated.simple_errors.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleErrorsService

class default__(WrappedSimpleErrorsService.default__):

    @staticmethod
    def WrappedSimpleErrors(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleErrors(wrapped_config)
        wrapped_client = SimpleErrorsShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleErrorsService.default__ = default__