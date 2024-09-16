// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleRecursiveShapeTypes.dfy"

module SimpleRecursiveShapeImpl refines AbstractSimpleRecursiveShapeOperations {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate GetRecursiveShapeEnsuresPublicly(input: GetRecursiveShapeInput, output: Result<GetRecursiveShapeOutput, Error>) {
    true
  }
  predicate GetRecursiveShapeKnownValueTestEnsuresPublicly(input: GetRecursiveShapeInput, output: Result<GetRecursiveShapeOutput, Error>) {
    true
  }
  method GetRecursiveShape(config: InternalConfig, input: GetRecursiveShapeInput )
    returns (output: Result<GetRecursiveShapeOutput, Error>) {
    var res := GetRecursiveShapeOutput(recursiveUnion := input.recursiveUnion);
    return Success(res);
  }

  // This method is only used for known-value testing. See "Known Value Tests" inside TestModels' README file.
  method GetRecursiveShapeKnownValueTest(config: InternalConfig, input: GetRecursiveShapeInput )
    returns (output: Result<GetRecursiveShapeOutput, Error>) {
    ValidateInput(input);
    var res := GetRecursiveShapeOutput(recursiveUnion := input.recursiveUnion);
    return Success(res);
  }

  method ValidateInput(input: GetRecursiveShapeInput) {

  }
}