// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleRefinementImpl.dfy"

module {:extern "simple.refinement.internaldafny"} SimpleRefinement refines AbstractSimpleRefinementService {
    import Operations = SimpleRefinementImpl

    function method DefaultSimpleRefinementConfig(): SimpleRefinementConfig {
        SimpleRefinementConfig
    }

    method SimpleRefinement(
        config: SimpleRefinementConfig
    ) returns (
        res: Result<SimpleRefinementClient, Error>
    ) {
        var client := new SimpleRefinementClient(Operations.Config);
        return Success(client);
    }

    class SimpleRefinementClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleRefinementClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
