// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "SimpleRecursiveShapeImpl.dfy"

module {:extern "simple.recursiveshape.internaldafny"} SimpleRecursiveShape refines AbstractSimpleRecursiveShapeService {
  import Operations = SimpleRecursiveShapeImpl

  function method DefaultSimpleRecursiveShapeConfig(): SimpleRecursiveShapeConfig {
    SimpleRecursiveShapeConfig
  }

  method SimpleRecursiveShape(config: SimpleRecursiveShapeConfig)
    returns (res: Result<SimpleRecursiveShapeClient, Error>) {
    var client := new SimpleRecursiveShapeClient(Operations.Config);
    return Success(client);
  }

  class SimpleRecursiveShapeClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleRecursiveShapeClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
