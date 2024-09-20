// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDependenciesTypes.dfy"
include "SimpleDependenciesImpl.dfy"

module {:extern "simple.dependencies.internaldafny" } SimpleDependencies refines AbstractSimpleDependenciesService {
  import Operations = SimpleDependenciesImpl
  import SimpleResourcesTypes
  import SimpleConstraints
  import ExtendableResource

  function method DefaultSimpleDependenciesConfig(): SimpleDependenciesConfig {
    SimpleDependenciesConfig(
      simpleResourcesConfig := Some(SimpleResourcesTypes.SimpleResourcesConfig(
        name := "default"
      )),
      // Passing in "None" as default.
      // This is a `function method`, so it cannot call methods or constructors.
      // ExtendableResource is created as a constructor or via a method call; ditto for SimpleConstraintsService.
      // As an workaround, a default is created in the SimpleDependencies method below.
      extendableResourceReference := None(),
      simpleConstraintsServiceReference := None(),
      specialString := Some("bw1and10")
    )
  }

  method SimpleDependencies(config: SimpleDependenciesConfig)
    returns (res: Result<SimpleDependenciesClient, Error>)
  {
    expect config.simpleResourcesConfig.Some?;
    expect config.specialString.Some?;

    // A default is created here, and not in the Default config, as this requires a constructor or method call to create.
    // DefaultConfig is a function, and this can't use methods or construct new objects.
    var extendableResourceReferenceToAssign;
    if config.extendableResourceReference.Some? {
      extendableResourceReferenceToAssign := config.extendableResourceReference.value;
    } else {
      extendableResourceReferenceToAssign := new ExtendableResource.ExtendableResource();
    }

    // A default is created here, and not in the Default config, as this requires a constructor or method call to create.
    // DefaultConfig is a function, and this can't use methods or construct new objects.
    var simpleConstraintsServiceReferenceToAssign;
    if config.simpleConstraintsServiceReference.Some? {
      simpleConstraintsServiceReferenceToAssign := config.simpleConstraintsServiceReference.value;
    } else {
      var newSimpleConstraintsServiceReference := SimpleConstraints.SimpleConstraints(SimpleConstraints.DefaultSimpleConstraintsConfig());
      expect newSimpleConstraintsServiceReference.Success?;
      simpleConstraintsServiceReferenceToAssign := newSimpleConstraintsServiceReference.value;
    }

    var configToAssign := Operations.Config(
      simpleResourcesConfig := config.simpleResourcesConfig.value,
      simpleConstraintsServiceReference := simpleConstraintsServiceReferenceToAssign,
      extendableResourceReference := extendableResourceReferenceToAssign,
      specialString := config.specialString.value
    );

    var client := new SimpleDependenciesClient(config := configToAssign);
    return Success(client);
  }

  class SimpleDependenciesClient... {
    predicate ValidState()
    {
      && Operations.ValidInternalConfig?(config)
      && History !in Operations.ModifiesInternalConfig(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }
    constructor(config: Operations.InternalConfig) {
      this.config := config;
      History := new ISimpleDependenciesClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
