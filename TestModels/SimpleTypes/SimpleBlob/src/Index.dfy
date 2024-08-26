// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleBlobImpl.dfy"

module {:extern "simple.types.blob.internaldafny" } SimpleBlob refines AbstractSimpleTypesBlobService {
    import Operations = SimpleBlobImpl

 function method DefaultSimpleBlobConfig(): SimpleBlobConfig {
    SimpleBlobConfig
 }

 method SimpleBlob(config: SimpleBlobConfig)
 returns (res: Result<SimpleBlobClient, Error>) {
    var client := new SimpleBlobClient(Operations.Config);
    return Success(client);
 }

 class SimpleBlobClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
 constructor(config: Operations.InternalConfig) {
    this.config := config;
    History := new ISimpleTypesBlobClientCallHistory();
    Modifies := Operations.ModifiesInternalConfig(config) + {History};
   }
 }

}
