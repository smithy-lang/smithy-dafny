// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleDocumentationImpl.dfy"

module {:extern "simple.documentation.internaldafny" } SimpleDocumentation refines AbstractSimpleDocumentationService {
  import Operations = SimpleDocumentationImpl

  function method DefaultSimpleDocumentationConfig(): SimpleDocumentationConfig {
    SimpleDocumentationConfig
  }

  method SimpleDocumentation(config: SimpleDocumentationConfig)
    returns (res: Result<SimpleDocumentationClient, Error>)
  {
    var client := new SimpleDocumentationClient(Operations.Config);
    return Success(client);
  }

  class SimpleDocumentationClient... {
    predicate ValidState() {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleDocumentationClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
