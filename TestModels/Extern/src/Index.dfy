// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleExternImpl.dfy"

module {:extern "simple.dafnyextern.internaldafny" } SimpleExtern refines AbstractSimpleDafnyExternService {
    import Operations = SimpleExternImpl

    function method DefaultSimpleExternConfig(): SimpleExternConfig {
        SimpleExternConfig
    }

    method SimpleExtern(config: SimpleExternConfig)
        returns (res: Result<SimpleExternClient, Error>)
    {
        var client := new SimpleExternClient(Operations.Config);
        return Success(client);
    }

    class SimpleExternClient... {
        predicate ValidState() {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }

        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleExternClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
