# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_aggregate_internaldafny_wrapped
from smithygenerated.simple_aggregate.client import SimpleAggregate
from smithygenerated.simple_aggregate.shim import SimpleAggregateShim
from smithygenerated.simple_aggregate.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_aggregate_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleAggregate(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleAggregate(wrapped_config)
        wrapped_client = SimpleAggregateShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_aggregate_internaldafny_wrapped.default__ = default__
