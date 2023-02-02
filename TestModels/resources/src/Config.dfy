// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//include "../Model/SimpleResourcesTypes.dfy"

module Config {
//  import opened StandardLibrary
//  import Types = SimpleResourcesTypes    

  datatype Config = Config(
    nameonly name: string
  )

  predicate method ValidInternalConfig?(config: Config)
  {
    && |config.name| > 0
  }

  function ModifiesInternalConfig(config: Config): set<object>
  {{}}
}
