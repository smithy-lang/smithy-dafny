// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypes.dfy"
include "./Config.dfy"
include "./SimpleResourcesOperations.dfy"

module SimpleResources refines AbstractSimpleResourcesService
{
  import Operations = SimpleResourcesOperations
  import Config

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
    :- Need(|config.name| > 0,
      Types.SimpleResourceException(
      message := "Length of name must be greater than 0")
    );
    var internalConfig: Operations.InternalConfig := Config.Config(
      name := config.name
    );

    var client := new SimpleResourcesClient(
      config := internalConfig
    );

    return Success(client);  
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
  
