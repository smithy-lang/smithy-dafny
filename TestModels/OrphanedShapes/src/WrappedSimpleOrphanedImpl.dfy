// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleOrphanedTypesWrapped.dfy"

module {:options "--function-syntax:4"} {:extern "simple.orphaned.internaldafny.wrapped"} WrappedSimpleOrphanedService refines WrappedAbstractSimpleOrphanedService {
  import WrappedService = SimpleOrphaned
  function WrappedDefaultSimpleOrphanedConfig(): SimpleOrphanedConfig {
    SimpleOrphanedConfig
  }
}
