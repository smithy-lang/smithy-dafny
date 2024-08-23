// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module {:extern "simple.callingawssdkfromlocalservice.internaldafny" } SimpleCallingAWSSDKFromLocalService refines AbstractSimpleCallingawssdkfromlocalserviceService {
    import Operations = SimpleCallingAWSSDKFromLocalServiceImpl

    function method DefaultSimpleCallingAWSSDKFromLocalServiceConfig(): SimpleCallingAWSSDKFromLocalServiceConfig {
       SimpleCallingAWSSDKFromLocalServiceConfig
    }

    method SimpleCallingAWSSDKFromLocalService(config: SimpleCallingAWSSDKFromLocalServiceConfig)
        returns (res: Result<SimpleCallingAWSSDKFromLocalServiceClient, Error>) 
    {
        var client := new SimpleCallingAWSSDKFromLocalServiceClient(Operations.Config);
        return Success(client);
    }

    class SimpleCallingAWSSDKFromLocalServiceClient... {
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