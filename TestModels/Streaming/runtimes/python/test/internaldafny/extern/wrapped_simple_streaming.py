# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_streaming.smithygenerated.simple_streaming.client import SimpleStreaming
from simple_streaming.smithygenerated.simple_streaming.shim import SimpleStreamingShim
from simple_streaming.smithygenerated.simple_streaming.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleStreamingService

class default__(WrappedSimpleStreamingService.default__):

    @staticmethod
    def WrappedSimpleStreaming(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleStreaming(wrapped_config)
        wrapped_client = SimpleStreamingShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleStreamingService.default__ = default__