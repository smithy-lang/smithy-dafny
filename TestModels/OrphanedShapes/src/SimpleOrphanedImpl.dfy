// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleOrphanedTypes.dfy"
include "OrphanedResource.dfy"

module SimpleOrphanedImpl refines AbstractSimpleOrphanedOperations  {

  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
}