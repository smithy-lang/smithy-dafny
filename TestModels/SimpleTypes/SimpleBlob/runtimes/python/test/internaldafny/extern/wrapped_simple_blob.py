# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_types_blob.smithygenerated.simple_types_blob.client import SimpleTypesBlob
from simple_types_blob.smithygenerated.simple_types_blob.shim import SimpleBlobShim
from simple_types_blob.smithygenerated.simple_types_blob.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesBlobService

class default__(WrappedSimpleTypesBlobService.default__):

    @staticmethod
    def WrappedSimpleBlob(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesBlob(wrapped_config)
        wrapped_client = SimpleBlobShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesBlobService.default__ = default__
