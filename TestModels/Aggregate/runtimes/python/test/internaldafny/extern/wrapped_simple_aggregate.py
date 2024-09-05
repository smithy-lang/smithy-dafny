# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_aggregate.smithygenerated.simple_aggregate.client import SimpleAggregate
from simple_aggregate.smithygenerated.simple_aggregate.shim import SimpleAggregateShim
from simple_aggregate.smithygenerated.simple_aggregate.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleAggregateService

class default__(WrappedSimpleAggregateService.default__):

    @staticmethod
    def WrappedSimpleAggregate(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleAggregate(wrapped_config)
        wrapped_client = SimpleAggregateShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleAggregateService.default__ = default__