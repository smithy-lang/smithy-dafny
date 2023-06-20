// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleEnumImpl.dfy"

module {:extern "simple.types.smithyenum.internaldafny" } SimpleEnum refines AbstractSimpleTypesSmithyEnumService {
    import Operations = SimpleEnumImpl

 function method DefaultSimpleEnumConfig(): SimpleEnumConfig {
    SimpleEnumConfig
 }

 method SimpleEnum(config: SimpleEnumConfig)
 returns (res: Result<SimpleEnumClient, Error>) {
    var client := new SimpleEnumClient(Operations.Config);
    return Success(client);
 }

 class SimpleEnumClient... {
   predicate ValidState()
   {
     && Operations.ValidInternalConfig?(config)
     && Modifies == Operations.ModifiesInternalConfig(config) + {History}
   }

   constructor(config: Operations.InternalConfig)
   {
     this.config := config;
     History := new ISimpleTypesEnumClientCallHistory();
     Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }
}
