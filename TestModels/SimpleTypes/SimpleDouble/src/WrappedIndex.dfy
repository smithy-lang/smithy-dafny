// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleTypesSmithyDoubleTypesWrapped.dfy"

module {:extern "simple.types.smithydouble.internaldafny.wrapped"} WrappedSimpleTypesDouble refines WrappedAbstractSimpleTypesSmithyDoubleService
{
  import WrappedService = SimpleDouble

  function method WrappedDefaultSimpleDoubleConfig(): SimpleDoubleConfig
  {
    WrappedService.DefaultSimpleDoubleConfig()
  }
}
