// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesBooleanTypes.dfy"

module SimpleBooleanImpl refines AbstractSimpleTypesBooleanOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
   predicate GetBooleanEnsuresPublicly(input: GetBooleanInput, output: Result<GetBooleanOutput, Error>) {
    true 
   }
 method GetBoolean ( config: InternalConfig,  input: GetBooleanInput )
 returns (output: Result<GetBooleanOutput, Error>) {
    expect input.value.Some?;
    // Verbose yet explicit statement: "input is a boolean, and it is either true or false"
    expect input.value.value == true || input.value.value == false;
    var res := GetBooleanOutput(value := input.value);
    // Verbose yet explicit statement: "output is a boolean, and it is either true or false"
    expect res.value.value == true || res.value.value == false;
    // Output must be the same as the input
    expect input.value.value == res.value.value;
    return Success(res);
 }
}