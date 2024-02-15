// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCodegenpatchesTypes.dfy"

module CodegenPatchesImpl refines AbstractSimpleCodegenpatchesOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  method GetString ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>)
  {  
    var res := GetStringOutput(value := input.value);

    return Success(res);
  }
}
