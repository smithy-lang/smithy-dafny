// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyEnumTypes.dfy"

module SimpleEnumImpl refines AbstractSimpleTypesSmithyEnumOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate GetEnumEnsuresPublicly(input: GetEnumInput, output: Result<GetEnumOutput, Error>) {
    true
  }
  predicate GetEnumFirstKnownValueTestEnsuresPublicly(input: GetEnumInput, output: Result<GetEnumOutput, Error>) {
    true
  }
  predicate GetEnumSecondKnownValueTestEnsuresPublicly(input: GetEnumInput, output: Result<GetEnumOutput, Error>) {
    true
  }
  predicate GetEnumThirdKnownValueTestEnsuresPublicly(input: GetEnumInput, output: Result<GetEnumOutput, Error>) {
    true
  }
  method GetEnum ( config: InternalConfig,  input: GetEnumInput )
  returns (output: Result<GetEnumOutput, Error>) {
    var res := GetEnumOutput(value := input.value);
    return Success(res);
  }

  // Known value tests. See "Known value test" in TestModels' README.
  method GetEnumFirstKnownValueTest ( config: InternalConfig,  input: GetEnumInput )
  returns (output: Result<GetEnumOutput, Error>) {
    expect input.value.Some?;
    expect input.value.value == FIRST;

    var res := GetEnumOutput(value := input.value);

    expect res.value.Some?;
    expect res.value.value == FIRST; 

    return Success(res);
  }

  method GetEnumSecondKnownValueTest ( config: InternalConfig,  input: GetEnumInput )
  returns (output: Result<GetEnumOutput, Error>) {
    expect input.value.Some?;
    expect input.value.value == SECOND;

    var res := GetEnumOutput(value := input.value);

    expect res.value.Some?;
    expect res.value.value == SECOND; 
    
    return Success(res);
  }

  method GetEnumThirdKnownValueTest ( config: InternalConfig,  input: GetEnumInput )
  returns (output: Result<GetEnumOutput, Error>) {
    expect input.value.Some?;
    expect input.value.value == THIRD;

    var res := GetEnumOutput(value := input.value);

    expect res.value.Some?;
    expect res.value.value == THIRD; 
    
    return Success(res);
  }
}
