// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleStringImpl.dfy"

module {:extern "simple.types.smithystring.internaldafny" } SimpleString refines AbstractSimpleTypesSmithyStringService {
    import Operations = SimpleStringImpl

    function method DefaultSimpleStringConfig(): SimpleStringConfig {
        SimpleStringConfig
    }

    method SimpleString(config: SimpleStringConfig)
    returns (res: Result<SimpleStringClient, Error>) {
        var client := new SimpleStringClient(Operations.Config);
        return Success(client);
    }

    class SimpleStringClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleTypesStringClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
