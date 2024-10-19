// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SQSExtendedImpl.dfy"

module {:extern "com.amazonaws.sqsextended.internaldafny" } SQSExtended refines AbstractAmazonSQSExtendedService {
  import Operations = AmazonSQSExtendedImpl

  function method DefaultSQSExtendedClientConfig(): SQSExtendedClientConfig {
    SQSExtendedClientConfig
  }

  method SQSExtended(config: SQSExtendedClientConfig)
    returns (res: Result<SQSExtendedClient, Error>)
  {
    var client := new SQSExtendedClient(Operations.Config);
    return Success(client);
  }

  class SQSExtendedClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new IAmazonSQSExtendedClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
