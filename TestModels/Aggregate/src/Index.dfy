// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleAggregateImpl.dfy"

module {:extern "simple.aggregate.internaldafny"} SimpleAggregate refines AbstractSimpleAggregateService {
    import Operations = SimpleAggregateImpl

    function method DefaultSimpleAggregateConfig(): SimpleAggregateConfig {
        SimpleAggregateConfig
    }

    method SimpleAggregate(config: SimpleAggregateConfig)
    returns (res: Result<SimpleAggregateClient, Error>) {
        var client := new SimpleAggregateClient(Operations.Config);
        return Success(client);
    }

    class SimpleAggregateClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleAggregateClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}