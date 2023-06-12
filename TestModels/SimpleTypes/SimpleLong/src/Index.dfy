// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleLongImpl.dfy"

module {:extern "simple.types.smithylong.internaldafny" } SimpleLong refines AbstractSimpleTypesSmithyLongService {
    import Operations = SimpleLongImpl

 function method DefaultSimpleLongConfig(): SimpleLongConfig {
    SimpleLongConfig
 }

 method SimpleLong(config: SimpleLongConfig)
 returns (res: Result<SimpleLongClient, Error>) {
    var client := new SimpleLongClient(Operations.Config);
    return Success(client);
 }

 class SimpleLongClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
   constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleTypesLongClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }

}
