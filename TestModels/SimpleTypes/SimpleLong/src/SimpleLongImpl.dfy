// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyLongTypes.dfy"

module SimpleLongImpl refines AbstractSimpleTypesSmithyLongOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate GetLongEnsuresPublicly(input: GetLongInput, output: Result<GetLongOutput, Error>) {
    true
  }
  predicate GetLongKnownValueTestEnsuresPublicly(input: GetLongInput, output: Result<GetLongOutput, Error>) {
    true
  }

  method GetLong ( config: InternalConfig,  input: GetLongInput )
    returns (output: Result<GetLongOutput, Error>)
  {
    expect input.value.Some?;
    ValidateLongType(input.value.value);

    var res := GetLongOutput(value := input.value);

    expect res.value.Some?;
    ValidateLongType(res.value.value);

    return Success(res);
  }

  // Known value test. See TestModels' README file.
  method GetLongKnownValueTest ( config: InternalConfig,  input: GetLongInput )
    returns (output: Result<GetLongOutput, Error>)
  {
    expect input.value.Some?;
    ValidateLongType(input.value.value);
    // Expect known value
    expect input.value.value == (33 as int64);

    var res := GetLongOutput(value := input.value);

    expect res.value.Some?;
    ValidateLongType(res.value.value);

    return Success(res);
  }

  method ValidateLongType(input: int64) {
    if (input >= 0) {
      // If input >= max int32 value, this is already a long
      if (input >= UInt.INT32_MAX_LIMIT as int64) {
        return;
      }
      // If adding max int value results in overflow, this is NOT a long
      expect input + (UInt.INT32_MAX_LIMIT as int64) > 0;
    }
    else if (input < 0) {
      // If input < min int32 value, this is already a long
      if (input < (-(UInt.INT32_MAX_LIMIT as int64))) {
        return;
      }
      // If adding negative max int value results in underflow, this is NOT a long
      expect input + (-(UInt.INT32_MAX_LIMIT as int64)) < 0;
    } else {
      // Must be >= 0 or < 0; i.e. comparable to numbers
      expect false;
    }
  }
}
