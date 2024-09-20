// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleTimestampImpl.dfy"

module {:extern "simple.types.timestamp.internaldafny" } SimpleTimestamp refines AbstractSimpleTypesTimestampService {
  import Operations = SimpleTypesTimestampImpl

  function method DefaultSimpleTimestampConfig(): SimpleTimestampConfig {
    SimpleTimestampConfig
  }

  method SimpleTimestamp(config: SimpleTimestampConfig)
    returns (res: Result<SimpleTimestampClient, Error>)
  {
    var client := new SimpleTimestampClient(Operations.Config);
    return Success(client);
  }

  class SimpleTimestampClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleTypesTimestampClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
