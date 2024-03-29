// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyPrimitivesTypes.dfy"
include "AwsCryptographyPrimitivesOperations.dfy"

module {:extern "software.amazon.cryptography.primitives.internaldafny" } Aws.Cryptography.Primitives refines AbstractAwsCryptographyPrimitivesService {
  import Operations = AwsCryptographyPrimitivesOperations

  function method DefaultCryptoConfig(): CryptoConfig {
    CryptoConfig
  }

  method AtomicPrimitives(config: CryptoConfig)
    // BEGIN MANUAL FIX
    returns (res: Result<AtomicPrimitivesClient, Error>)
    // END MANUAL FIX
    ensures res.Success? ==>
              && res.value is AtomicPrimitivesClient
  {
    var client := new AtomicPrimitivesClient(Operations.Config);
    // BEGIN MANUAL FIX
    return Success(client);
    // END MANUAL FIX
  }

  class AtomicPrimitivesClient... {

    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IAwsCryptographicPrimitivesClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

  }
}
