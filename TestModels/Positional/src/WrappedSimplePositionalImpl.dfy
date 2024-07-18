// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimplePositionalTypesWrapped.dfy"

module {:options "--function-syntax:4"} {:extern "simple.positional.internaldafny.wrapped"} WrappedSimplePositionalService refines WrappedAbstractSimplePositionalService {
  import WrappedService = SimplePositional
  function WrappedDefaultSimplePositionalConfig(): SimplePositionalConfig {
    SimplePositionalConfig
  }
}
