// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleMultiplemodelsDependencyprojectImpl.dfy"

module {:extern "simple.multiplemodels.dependencyproject.internaldafny" } DependencyProject refines AbstractSimpleMultiplemodelsDependencyprojectService {
    import Operations = SimpleMultiplemodelsDependencyprojectImpl

    function method DefaultDependencyProjectConfig(): DependencyProjectConfig {
       DependencyProjectConfig
    }

    method DependencyProject(config: DependencyProjectConfig)
    returns (res: Result<DependencyProjectClient, Error>) {
        var client := new DependencyProjectClient(Operations.Config);
        return Success(client);
    }

    class DependencyProjectClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new IDependencyProjectClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
