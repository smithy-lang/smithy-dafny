// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesEnumV2Types.dfy"

module SimpleEnumV2Impl refines AbstractSimpleTypesEnumV2Operations {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig) { true }
  function ModifiesInternalConfig(config: InternalConfig): set<object> { {} }
  predicate GetEnumV2EnsuresPublicly(input: GetEnumV2Input, output: Result<GetEnumV2Output, Error>) {
    true
  }
  predicate GetEnumV2FirstKnownValueTestEnsuresPublicly(input: GetEnumV2Input, output: Result<GetEnumV2Output, Error>) {
    true
  }
  predicate GetEnumV2SecondKnownValueTestEnsuresPublicly(input: GetEnumV2Input, output: Result<GetEnumV2Output, Error>) {
    true
  }
  predicate GetEnumV2ThirdKnownValueTestEnsuresPublicly(input: GetEnumV2Input, output: Result<GetEnumV2Output, Error>) {
    true
  }
  method GetEnumV2(config: InternalConfig, input: GetEnumV2Input)
    returns (output: Result<GetEnumV2Output, Error>)
  {
    var res := GetEnumV2Output(value := input.value);
    return Success(res);
  }

  // Known value tests. See "Known value test" in TestModels' README.
  method GetEnumV2FirstKnownValueTest(config: InternalConfig, input: GetEnumV2Input)
    returns (output: Result<GetEnumV2Output, Error>)
  {
    expect input.value.Some?;
    expect input.value.value == FIRST;

    var res := GetEnumV2Output(value := input.value);

    expect res.value.Some?;
    expect res.value.value == FIRST;

    return Success(res);
  }

  method GetEnumV2SecondKnownValueTest(config: InternalConfig, input: GetEnumV2Input)
    returns (output: Result<GetEnumV2Output, Error>)
  {
    expect input.value.Some?;
    expect input.value.value == SECOND;

    var res := GetEnumV2Output(value := input.value);

    expect res.value.Some?;
    expect res.value.value == SECOND;

    return Success(res);
  }

  method GetEnumV2ThirdKnownValueTest(config: InternalConfig, input: GetEnumV2Input)
    returns (output: Result<GetEnumV2Output, Error>)
  {
    expect input.value.Some?;
    expect input.value.value == THIRD;

    var res := GetEnumV2Output(value := input.value);

    expect res.value.Some?;
    expect res.value.value == THIRD;

    return Success(res);
  }
}
