// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleResourcesTypesWrapped.dfy"

//TODO: This will not compile in Go because https://t.corp.amazon.com/P153280434
//For now, the shim has been checked-in instead of being generated on the fly.
module {:extern "simple.resources.internaldafny.wrapped"} WrappedSimpleResources refines WrappedAbstractSimpleResourcesService
{
  import WrappedService = SimpleResources

  function method WrappedDefaultSimpleResourcesConfig(): SimpleResourcesConfig
  {
    WrappedService.DefaultSimpleResourcesConfig()
  }
}
