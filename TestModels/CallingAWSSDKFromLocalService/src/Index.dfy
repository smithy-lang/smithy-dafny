// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"
include "SimpleCallingawssdkfromlocalserviceImpl.dfy"

module {:extern "simple.callingawssdkfromlocalservice.internaldafny" } SimpleCallingawssdkfromlocalservice refines AbstractSimpleCallingawssdkfromlocalserviceService {
  import Operations = SimpleCallingawssdkfromlocalserviceImpl

  function method DefaultSimpleCallingawssdkfromlocalserviceConfig(): SimpleCallingawssdkfromlocalserviceConfig {
    SimpleCallingawssdkfromlocalserviceConfig
  }

  method SimpleCallingawssdkfromlocalservice(config: SimpleCallingawssdkfromlocalserviceConfig)
    returns (res: Result<SimpleCallingawssdkfromlocalserviceClient, Error>)
  {
    var client := new SimpleCallingawssdkfromlocalserviceClient(Operations.Config);
    return Success(client);
  }

  class SimpleCallingawssdkfromlocalserviceClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleCallingAWSSDKFromLocalServiceClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
