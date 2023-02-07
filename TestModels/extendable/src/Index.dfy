// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypes.dfy"
include "./SimpleExtendableResourcesOperations.dfy"

module SimpleExtendableResources refines AbstractSimpleExtendableResourcesService
{
  import Operations = SimpleExtendableResourcesOperations
  
  function method DefaultSimpleExtendableResourcesConfig(): SimpleExtendableResourcesConfig
  {SimpleExtendableResourcesConfig()}

  method SimpleExtendableResources(
    config: SimpleExtendableResourcesConfig
  ) returns (
    res: Result<SimpleExtendableResourcesClient, Error>
  )
  {
    // SimpleExtendableResourcesConfig is an empty structure,
    // so the `config` parameter is ignored,
    // but smithy-dafny generates it,
    // so the implementation MUST have it.
    var internalConfig := Operations.Config();

    if Operations.ValidInternalConfig?(internalConfig) {
      var client := new SimpleExtendableResourcesClient(
        config := internalConfig
      );
      return Success(client);
    } else {
      return Failure(Types.SimpleResourceException(
        message := "Invalid Internal Config. Should be impossible.")
      );
    }
  }

  class SimpleExtendableResourcesClient...
  {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && History !in Operations.ModifiesInternalConfig(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}      
    }

    constructor(
      config: Operations.InternalConfig
    )
    {
      this.config := config;
      History := new ISimpleExtendableResourcesClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
