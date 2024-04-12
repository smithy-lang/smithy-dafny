// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleEnumImpl.dfy"

module {:extern "simple.types.enumv2.internaldafny" } SimpleEnumV2 refines AbstractSimpleTypesEnumV2Service {
    import Operations = SimpleEnumV2Impl

 function method DefaultSimpleEnumV2Config(): SimpleEnumV2Config {
    SimpleEnumV2Config
 }

 method SimpleEnumV2(config: SimpleEnumV2Config)
 returns (res: Result<SimpleEnumV2Client, Error>) {
    var client := new SimpleEnumV2Client(Operations.Config);
    return Success(client);
 }

 class SimpleEnumV2Client... {
   predicate ValidState()
   {
     && Operations.ValidInternalConfig?(config)
     && Modifies == Operations.ModifiesInternalConfig(config) + {History}
   }

   constructor(config: Operations.InternalConfig)
   {
     this.config := config;
     History := new ISimpleTypesEnumV2ClientCallHistory();
     Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }
}
