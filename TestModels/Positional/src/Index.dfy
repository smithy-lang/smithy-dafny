// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimplePositionalImpl.dfy"

module {:extern "simple.positional.internaldafny" } SimplePositional refines AbstractSimplePositionalService {
  import Operations = SimplePositionalImpl

  function method DefaultSimplePositionalConfig(): SimplePositionalConfig {
    SimplePositionalConfig
  }

  method SimplePositional(config: SimplePositionalConfig)
    returns (res: Result<SimplePositionalClient, Error>)
  {
    var client := new SimplePositionalClient(Operations.Config);
    return Success(client);
  }

  class SimplePositionalClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimplePositionalClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
