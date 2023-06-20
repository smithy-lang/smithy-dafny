// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleConstructorImpl.dfy"

module {:extern "simple.constructor.internaldafny" } SimpleConstructor refines AbstractSimpleConstructorService {
    import Operations = SimpleConstructorImpl

    function method DefaultSimpleConstructorConfig(): SimpleConstructorConfig {
        SimpleConstructorConfig(
            blobValue:= Some([0]),
            booleanValue:= Some(false),
            stringValue:= Some(""),
            integerValue:= Some(0),
            longValue:= Some(0)
        )
    }

    method SimpleConstructor(config: SimpleConstructorConfig)
        returns (res: Result<SimpleConstructorClient, Error>)
    {
        var configToAssign := Operations.Config(
            blobValue := config.blobValue.UnwrapOr([0]),
            booleanValue := config.booleanValue.UnwrapOr(true),
            stringValue:= config.stringValue.UnwrapOr(""),
            integerValue:= config.integerValue.UnwrapOr(0),
            longValue:= config.longValue.UnwrapOr(0)
        );
        var client := new SimpleConstructorClient(config := configToAssign);
        return Success(client);
    }

    class SimpleConstructorClient... {
        predicate ValidState() {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }

        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleConstructorClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
