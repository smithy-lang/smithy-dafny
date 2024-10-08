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
  method GetRecursiveShape(config: InternalConfig, input: GetRecursiveShapeInput )
    returns (output: Result<GetRecursiveShapeOutput, Error>) {
    var res := GetRecursiveShapeOutput(recursiveUnion := input.recursiveUnion);
    return Success(res);
  }
}