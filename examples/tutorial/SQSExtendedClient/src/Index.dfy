// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SQSExtendedImpl.dfy"

module {:extern "polymorph.tutorial.sqsextended.internaldafny" } SQSExtended refines AbstractPolymorphTutorialSqsextendedService {
  import Operations = AmazonSQSExtendedImpl

  method SQSExtended(config: SQSExtendedClientConfig)
    returns (res: Result<SQSExtendedClient, Error>)
    ensures res.Success? ==> 
      && res.value.ValidState()
      && fresh(res.value.History)
  {
    var client := new SQSExtendedClient(Operations.Config(
                                        sqsClient := config.sqsClient
                                        ));
    return Success(client);
  }

  class SQSExtendedClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && History !in Operations.ModifiesInternalConfig(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new IAmazonSQSExtendedClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
