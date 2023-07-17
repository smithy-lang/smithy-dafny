# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.aggregate.internaldafny.wrapped
from simple_aggregate.smithy_generated.simple_aggregate.client import SimpleAggregate
from simple_aggregate.smithy_generated.simple_aggregate.shim import SimpleAggregateShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleAggregate(config):
    wrapped_config = config
    impl = SimpleAggregate(wrapped_config)
    wrapped_client = SimpleAggregateShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.aggregate.internaldafny.wrapped.default__.WrappedSimpleAggregate = WrappedSimpleAggregate
