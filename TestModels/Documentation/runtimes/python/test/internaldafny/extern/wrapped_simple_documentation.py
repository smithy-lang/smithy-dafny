# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_documentation.smithygenerated.simple_documentation.client import SimpleDocumentation
from simple_documentation.smithygenerated.simple_documentation.shim import SimpleDocumentationShim
from simple_documentation.smithygenerated.simple_documentation.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleDocumentationService

class default__(WrappedSimpleDocumentationService.default__):

    @staticmethod
    def WrappedSimpleDocumentation(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleDocumentation(wrapped_config)
        wrapped_client = SimpleDocumentationShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleDocumentationService.default__ = default__