// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module {:extern "simple.callingawssdkfromlocalservice.internaldafny.types" } SimpleCallingawssdkfromlocalserviceTypes refines AbstractSimpleCallingawssdkfromlocalserviceService {
    import Operations = SimpleCallingAWSSDKFromLocalServiceImpl

    function method DefaultSimpleCallingAWSSDKFromLocalServiceImplConfig(): SimpleCallingAWSSDKFromLocalServiceImplConfig {
       SimpleCallingAWSSDKFromLocalServiceImplConfig
    }

    method SimpleCallingAWSSDKFromLocal(config: SimpleCallingAWSSDKFromLocalServiceImplConfig)
    returns (res: Result<SimpleCallingAWSSDKFromLocalClient, Error>) {
        var client := new SimpleCallingAWSSDKFromLocalClient(Operations.Config);
        return Success(client);
    }

    class SimpleCallingAWSSDKFromLocalClient... {
        predicate ValidState()
        {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }
        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleCallingAWSSDKFromLocalClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}