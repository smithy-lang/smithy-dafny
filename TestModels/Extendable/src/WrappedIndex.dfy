// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleExtendableResourcesTypesWrapped.dfy"

module
  {:extern "simple_extendable_resources_internaldafny_wrapped"}
  WrappedSimpleExtendableResources refines WrappedAbstractSimpleExtendableResourcesService
{
  import WrappedService = SimpleExtendableResources

  function method WrappedDefaultSimpleExtendableResourcesConfig(): SimpleExtendableResourcesConfig
  {
    SimpleExtendableResourcesConfig
  }
}
