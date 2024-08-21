// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypes.dfy"
include "./SimpleExtendableResourcesOperations.dfy"

module {:extern "simple.extendable.resources.internaldafny"} SimpleExtendableResources refines AbstractSimpleExtendableResourcesService
{
  import Operations = SimpleExtendableResourcesOperations
  
  function method DefaultSimpleExtendableResourcesConfig(): SimpleExtendableResourcesConfig
  {SimpleExtendableResourcesConfig()}

  method SimpleExtendableResources(
    // SimpleExtendableResourcesConfig is an empty structure,
    // so the `config` parameter is ignored,
    // but smithy-dafny generates it,
    // so the implementation MUST have it.
    config: SimpleExtendableResourcesConfig
  ) returns (
    res: Result<SimpleExtendableResourcesClient, Error>
  )
  {
    var internalConfig := Operations.Config();
    var client := new SimpleExtendableResourcesClient(
      config := internalConfig
    );
    return Success(client);
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
