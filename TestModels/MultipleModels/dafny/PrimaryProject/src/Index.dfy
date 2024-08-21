// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleMultiplemodelsPrimaryprojectImpl.dfy"

module {:extern "simple.multiplemodels.primaryproject.internaldafny" } PrimaryProject refines AbstractSimpleMultiplemodelsPrimaryprojectService {
    import Operations = SimpleMultiplemodelsPrimaryprojectImpl

    function method DefaultPrimaryProjectConfig(): PrimaryProjectConfig {
       PrimaryProjectConfig
    }

    method PrimaryProject(config: PrimaryProjectConfig)
    returns (res: Result<PrimaryProjectClient, Error>) {
        var client := new PrimaryProjectClient(Operations.Config);
        return Success(client);
    }

    class PrimaryProjectClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new IPrimaryProjectClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
