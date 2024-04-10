// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleTypesSmithyDoubleTypes.dfy"
include "./SimpleSmithyDoubleOperations.dfy"

module {:extern "simple.types.smithydouble.internaldafny" } SimpleDouble refines AbstractSimpleTypesSmithyDoubleService {
 import Operations = SimpleSmithyDoubleOperations

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
