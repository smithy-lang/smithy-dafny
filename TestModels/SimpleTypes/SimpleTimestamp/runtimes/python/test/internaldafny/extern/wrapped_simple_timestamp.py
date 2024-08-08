# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports 
from simple_types_timestamp.smithygenerated.simple_types_timestamp.client import SimpleTypesTimestamp
from simple_types_timestamp.smithygenerated.simple_types_timestamp.shim import SimpleTimestampShim
from simple_types_timestamp.smithygenerated.simple_types_timestamp.config import dafny_config_to_smithy_config
import standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleTypesTimestampService

class default__(WrappedSimpleTypesTimestampService.default__):

    @staticmethod
    def WrappedSimpleTimestamp(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesTimestamp(wrapped_config)
        wrapped_client = SimpleTimestampShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleTypesTimestampService.default__ = default__
