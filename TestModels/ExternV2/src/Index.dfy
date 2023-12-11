// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleExternV2Impl.dfy"

replaceable module SimpleExternV2 refines AbstractSimpleDafnyExternV2Service {
    import Operations = SimpleExternV2Impl

    function method DefaultSimpleExternV2Config(): SimpleExternV2Config {
        SimpleExternV2Config
    }

    method SimpleExternV2(config: SimpleExternV2Config)
        returns (res: Result<ISimpleExternV2Client, Error>)
    {
        var client := new SimpleExternV2Client(Operations.Config);
        return Success(client);
    }

    class SimpleExternV2Client... {
        predicate ValidState() {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }

        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ISimpleExternV2ClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
