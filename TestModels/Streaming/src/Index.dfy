// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleStreamingImpl.dfy"

module {:extern "simple.streaming.internaldafny"} SimpleStreaming refines AbstractSimpleStreamingService {
  import Operations = SimpleStreamingImpl

  function method DefaultSimpleStreamingConfig(): SimpleStreamingConfig {
    SimpleStreamingConfig
  }

  method SimpleStreaming(config: SimpleStreamingConfig)
    returns (res: Result<SimpleStreamingClient, Error>)
  {
    var client := new SimpleStreamingClient(Operations.Config);
    return Success(client);
  }

  class SimpleStreamingClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleStreamingClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
