// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleTypesDoubleTypes.dfy"
include "./SimpleDoubleOperations.dfy"

module {:extern "Dafny.Simple.Types.Double" } SimpleDouble refines AbstractSimpleTypesDoubleService {
 import Operations = SimpleDoubleOperations

 function method DefaultSimpleDoubleConfig(): SimpleDoubleConfig {
    SimpleDoubleConfig
 }

 method SimpleDouble(config: SimpleDoubleConfig)
 returns (res: Result<SimpleDoubleClient, Error>) {
    var client := new SimpleDoubleClient(Operations.Config);
    return Success(client);
 }

 class SimpleDoubleClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleTypesDoubleClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }

}
