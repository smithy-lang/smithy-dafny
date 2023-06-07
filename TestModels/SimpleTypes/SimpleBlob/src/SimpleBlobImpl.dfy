// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesBlobTypes.dfy"

module SimpleBlobImpl refines AbstractSimpleTypesBlobOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate GetBlobEnsuresPublicly(input: GetBlobInput, output: Result<GetBlobOutput, Error>) {
    true
  }
  predicate GetBlobKnownValueTestEnsuresPublicly(input: GetBlobInput, output: Result<GetBlobOutput, Error>) {
    true
  }
  method GetBlob ( config: InternalConfig,  input: GetBlobInput )
    returns (output: Result<GetBlobOutput, Error>)
  {
    expect input.value.Some?;
    ValidateBlobType(input.value.value);

    var res := GetBlobOutput(value := input.value);
    expect res.value.Some?;
    ValidateBlobType(res.value.value);

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
  }

  // This method is only used for known-value testing. See "Known Value Tests" inside TestModels' README file.
  method GetBlobKnownValueTest ( config: InternalConfig,  input: GetBlobInput )
    returns (output: Result<GetBlobOutput, Error>)
  {
    expect input.value.Some?;
    ValidateBlobType(input.value.value);

    // Expect known value
    expect input.value.value == [0x0, 0x2, 0x4];

    var res := GetBlobOutput(value := input.value);
    expect res.value.Some?;
    ValidateBlobType(res.value.value);

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
 }


 method ValidateBlobType(input: seq<UInt.uint8>)
 {
    // Validate seq<uint8> type properties on input
    // Input can contain items: "input has a measurable length of at least 0"
    expect |input| >= 0;

    // Validate uint8 type properties on input values
    for i := 0 to |input| {
      // Input is index-accessible, which means input is seq-like rather than a set
      var inputElement := input[i];
      // "Input can be interpreted as any valid uint8"
      expect inputElement >= 0x0;
    }
    // If input does not contain any values, we aren't interested in validating per-element properties on it
  }
}