// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleOrphanedImpl.dfy"

module {:extern "simple.orphaned.internaldafny" } SimpleOrphaned refines AbstractSimpleOrphanedService {
  import Operations = SimpleOrphanedImpl

  function method DefaultSimpleOrphanedConfig(): SimpleOrphanedConfig {
    SimpleOrphanedConfig
  }

  method SimpleOrphaned(config: SimpleOrphanedConfig)
    returns (res: Result<SimpleOrphanedClient, Error>)
  {
    var client := new SimpleOrphanedClient(Operations.Config);
    return Success(client);
  }

  class SimpleOrphanedClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleOrphanedClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
