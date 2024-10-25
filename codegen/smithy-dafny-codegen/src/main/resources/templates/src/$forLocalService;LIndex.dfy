// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "$sdkID:LImpl.dfy"

module {:extern "$namespace:L.internaldafny" } $sdkID:L refines Abstract$dafnyModuleName:LService {
  import Operations = $service:LImpl

  function method Default$serviceConfig:L(): $serviceConfig:L {
    $serviceConfig:L
  }

  method $sdkID:L(config: $serviceConfig:L)
    returns (res: Result<$sdkID:LClient, Error>)
  {
    var client := new $sdkID:LClient(Operations.Config);
    return Success(client);
  }

  class $sdkID:LClient... {
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
