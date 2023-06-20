// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleErrorsImpl.dfy"

module {:extern "simple.errors.internaldafny" } SimpleErrors refines AbstractSimpleErrorsService {
  import Operations = SimpleErrorsImpl

  function method DefaultSimpleErrorsConfig(): SimpleErrorsConfig {
    SimpleErrorsConfig
  }

  method SimpleErrors(config: SimpleErrorsConfig)
    returns (res: Result<SimpleErrorsClient, Error>)
  {
    var client := new SimpleErrorsClient(Operations.Config);
    return Success(client);
  }

  class SimpleErrorsClient... {
    predicate ValidState() {
       && Operations.ValidInternalConfig?(config)
       && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
       this.config := config;
       History := new ISimpleErrorsClientCallHistory();
       Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
