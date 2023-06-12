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
    History := new ISimpleBooleanClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }

}
/*
dafny \
                -vcsCores:2 \
                -compileTarget:py \
                -spillTargetCode:3 \
                -runAllTests:1 \
                -compile:0 \
                -optimizeErasableDatatypeWrapper:0 \
                -useRuntimeLib \
                -out runtimes/java/TestsFromDafny \
                `find ./test -name '*.dfy'` \
                -library:src/Index.dfy
*/
