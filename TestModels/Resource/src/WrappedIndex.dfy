// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypesWrapped.dfy"

module {:extern "simple.resources.internaldafny.wrapped"} WrappedSimpleResources refines WrappedAbstractSimpleResourcesService
{
  import WrappedService = SimpleResources

  function method WrappedDefaultSimpleResourcesConfig(): SimpleResourcesConfig
  {
    WrappedService.DefaultSimpleResourcesConfig()
  }
}
