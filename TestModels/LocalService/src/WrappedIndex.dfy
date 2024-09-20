// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleLocalServiceTypesWrapped.dfy"

module {:extern "simple.localservice.internaldafny.wrapped"} WrappedSimpleLocalService refines WrappedAbstractSimpleLocalServiceService
{
  import WrappedService = SimpleLocalService

  function method WrappedDefaultSimpleLocalServiceConfig(): SimpleLocalServiceConfig
  {
    WrappedService.DefaultSimpleLocalServiceConfig()
  }
}
