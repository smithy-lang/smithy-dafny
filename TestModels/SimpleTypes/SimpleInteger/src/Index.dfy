// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleIntegerImpl.dfy"

module SimpleInteger refines AbstractSimpleTypesIntegerService {
    import Operations = SimpleIntegerImpl

    function method DefaultSimpleIntegerConfig(): SimpleIntegerConfig {
       SimpleIntegerConfig
    }

    method SimpleInteger(config: SimpleIntegerConfig)
    returns (res: Result<SimpleIntegerClient, Error>) {
        var client := new SimpleIntegerClient(Operations.Config);
        return Success(client);
    }

    class SimpleIntegerClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleTypesIntegerClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
