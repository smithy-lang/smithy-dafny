// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "$service:LImpl.dfy"

module {:extern "$namespace:L.internaldafny" } $service:L refines Abstract$service:LService {
  import Operations = $service:LImpl

  function method Default$serviceConfig:L(): $serviceConfig:L {
    $serviceConfig:L
  }

  method $service:L(config: $serviceConfig:L)
    returns (res: Result<$service:LClient, Error>)
  {
    var client := new $service:LClient(Operations.Config);
    return Success(client);
  }

  class $service:LClient... {
    predicate ValidState() {
       && Operations.ValidInternalConfig?(config)
       && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
       this.config := config;
       History := new I$service:LClientCallHistory();
       Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
