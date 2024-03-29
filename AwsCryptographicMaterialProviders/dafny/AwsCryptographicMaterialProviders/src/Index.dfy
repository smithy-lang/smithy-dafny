// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AwsCryptographyMaterialProvidersOperations.dfy"

module
  {:extern "software.amazon.cryptography.materialproviders.internaldafny" }
  MaterialProviders refines AbstractAwsCryptographyMaterialProvidersService
{

  import Operations = AwsCryptographyMaterialProvidersOperations
  import Aws.Cryptography.Primitives
  import Crypto = AwsCryptographyPrimitivesTypes

  function method DefaultMaterialProvidersConfig(): MaterialProvidersConfig
  {
    MaterialProvidersConfig
  }

  method MaterialProviders(config: MaterialProvidersConfig)
    returns (res: Result<MaterialProvidersClient, Error>)
    ensures res.Success? ==>
              && res.value is MaterialProvidersClient
  {
    var maybeCrypto := Primitives.AtomicPrimitives();
    var cryptoPrimitivesX : Crypto.IAwsCryptographicPrimitivesClient :- maybeCrypto
    .MapFailure(e => Types.AwsCryptographyPrimitives(e));
    assert cryptoPrimitivesX is Primitives.AtomicPrimitivesClient;
    var cryptoPrimitives := cryptoPrimitivesX as Primitives.AtomicPrimitivesClient;

    var client := new MaterialProvidersClient(Operations.Config( crypto := cryptoPrimitives ));
    return Success(client);
  }

  class MaterialProvidersClient... {

    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IAwsCryptographicMaterialProvidersClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

  }

}
