// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleBooleanImpl.dfy"

module {:extern "simple.types.boolean.internaldafny" } SimpleBoolean refines AbstractSimpleTypesBooleanService {
    import Operations = SimpleBooleanImpl

 function method DefaultSimpleBooleanConfig(): SimpleBooleanConfig {
    SimpleBooleanConfig
 }

 method SimpleBoolean(config: SimpleBooleanConfig)
 returns (res: Result<SimpleBooleanClient, Error>) {
    var client := new SimpleBooleanClient(Operations.Config);
    return Success(client);
 }

 class SimpleBooleanClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleTypesBooleanClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }

}
