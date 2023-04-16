// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleLocalServiceTypes.dfy"

module SimpleLocalServiceOperations refines AbstractSimpleLocalServiceOperations {

  datatype Config = Config

  type InternalConfig = Config
    
  predicate method ValidInternalConfig?(config: InternalConfig)
  {true}

  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
    
}
