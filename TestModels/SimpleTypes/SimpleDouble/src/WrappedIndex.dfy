
// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleTypesDoubleTypesWrapped.dfy"

module
  {:extern "Dafny.Simple.Types.Double.Wrapped"}
  WrappedSimpleTypesDouble refines WrappedAbstractSimpleTypesDoubleService
{
  import WrappedService = SimpleDouble

  function method WrappedDefaultSimpleDoubleConfig(): SimpleDoubleConfig
  {
    WrappedService.DefaultSimpleDoubleConfig()
  }
}
