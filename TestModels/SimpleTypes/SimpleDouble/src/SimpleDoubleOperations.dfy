// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleTypesDoubleTypes.dfy"

module SimpleDoubleOperations refines AbstractSimpleTypesDoubleOperations {
  datatype Config = Config

  type InternalConfig = Config

  predicate method ValidInternalConfig?(config: InternalConfig)
  {true}

  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
  
  predicate GetDoubleEnsuresPublicly(
    input: GetDoubleInput,
    output: Result<GetDoubleOutput, Error>
  ) {true}

  method GetDouble(
    config: InternalConfig,
    input: GetDoubleInput
  ) returns (
    output: Result<GetDoubleOutput, Error>
  )
  {
    expect input.value.Some?;
    var check := ValidateDoubleType(input.value.value);
    expect check;

    
    var result: GetDoubleOutput := GetDoubleOutput(
      value := input.value
    );
    return Success(result);  
  }

  predicate ValidDoubleType(input: seq<uint8>)
  {|input| == 8}

  method ValidateDoubleType(
    input: seq<uint8>
  ) returns (
    output: bool
  )
    ensures ValidDoubleType(input) ==> output == true
  {
    return |input| == 8;
  }
}
