// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./SimpleResourcesOperations.dfy"

module {:extern "simple.resources.internaldafny"} SimpleResources refines AbstractSimpleResourcesService
{
  import Operations = SimpleResourcesOperations

  function method DefaultSimpleResourcesConfig(): SimpleResourcesConfig
  {
    SimpleResourcesConfig(
      name := "default"
    )
  }

  method SimpleResources(
    config: SimpleResourcesConfig
  ) returns (
    res: Result<SimpleResourcesClient, Error>
  )
  {
    var internalConfig: Operations.InternalConfig := Operations.Config(
      name := config.name
    );

    if Operations.ValidInternalConfig?(internalConfig) {
      var client := new SimpleResourcesClient(
        config := internalConfig
      );
      return Success(client);
    } else {
      return Failure(Types.SimpleResourcesException(
        message := "Length of name must be greater than 0")
     );
    }
  }

  class SimpleResourcesClient...
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
      History := new ISimpleResourcesClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
  
