# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_types_blob_internaldafny_wrapped
from simple_blob.smithygenerated.client import SimpleTypesBlob
from simple_blob.smithygenerated.shim import SimpleBlobShim
import Wrappers

@staticmethod
def WrappedSimpleBlob(config):
    wrapped_config = config
    impl = SimpleTypesBlob(wrapped_config)
    wrapped_client = SimpleBlobShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_types_blob_internaldafny_wrapped.default__.WrappedSimpleBlob = WrappedSimpleBlob
