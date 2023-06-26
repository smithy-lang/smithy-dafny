# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.types.blob.internaldafny.wrapped
from simple_blob.smithy_generated.simple_blob.client import SimpleTypesBlob
from simple_blob.smithy_generated.simple_blob.shim import SimpleBlobShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleBlob(config):
    wrapped_config = config
    impl = SimpleTypesBlob(wrapped_config)
    wrapped_client = SimpleBlobShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.blob.internaldafny.wrapped.default__.WrappedSimpleBlob = WrappedSimpleBlob
