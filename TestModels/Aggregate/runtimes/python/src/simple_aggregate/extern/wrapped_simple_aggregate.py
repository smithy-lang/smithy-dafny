# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_aggregate_internaldafny_wrapped
from simple_aggregate.smithygenerated.config import dafny_config_to_smithy_config
from simple_aggregate.smithygenerated.client import SimpleAggregate
from simple_aggregate.smithygenerated.shim import SimpleAggregateShim
import Wrappers

@staticmethod
def WrappedSimpleAggregate(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleAggregate(wrapped_config)
    wrapped_client = SimpleAggregateShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_aggregate_internaldafny_wrapped.default__.WrappedSimpleAggregate = WrappedSimpleAggregate
