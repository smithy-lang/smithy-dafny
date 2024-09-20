// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleLocalServiceTypes.dfy"
include "./SimpleLocalServiceOperations.dfy"

module {:extern "simple.localservice.internaldafny"} SimpleLocalService refines AbstractSimpleLocalServiceService
{
  import Operations = SimpleLocalServiceOperations

  function method DefaultSimpleLocalServiceConfig(): SimpleLocalServiceConfig
  {
    SimpleLocalServiceConfig
  }

  method SimpleLocalService(
    config: SimpleLocalServiceConfig
  ) returns (
    res: Result<SimpleLocalServiceClient, Error>
  )
  {
    var client := new SimpleLocalServiceClient(Operations.Config);
    return Success(client);
  }

  class SimpleLocalServiceClient...
  {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(
      config: Operations.InternalConfig
    )
    {
      this.config := config;
      History := new ISimpleLocalServiceClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}

