// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "LanguageSpecificLogicImpl.dfy"

module {:extern "language.specific.logic.internaldafny"} LanguageSpecificLogic refines AbstractLanguageSpecificLogicService {
    import Operations = LanguageSpecificLogicImpl

    function method DefaultLanguageSpecificLogicConfig(): LanguageSpecificLogicConfig {
        LanguageSpecificLogicConfig
    }

    method LanguageSpecificLogic(config: LanguageSpecificLogicConfig)
        returns (res: Result<LanguageSpecificLogicClient, Error>)
    {
        var client := new LanguageSpecificLogicClient(Operations.Config);
        return Success(client);
    }

    class LanguageSpecificLogicClient... {
        predicate ValidState() {
            && Operations.ValidInternalConfig?(config)
            && Modifies == Operations.ModifiesInternalConfig(config) + {History}
        }

        constructor(config: Operations.InternalConfig) {
            this.config := config;
            History := new ILanguageSpecificLogicClientCallHistory();
            Modifies := Operations.ModifiesInternalConfig(config) + {History};
        }
    }
}
