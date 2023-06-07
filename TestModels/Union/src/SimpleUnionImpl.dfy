// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleUnionTypes.dfy"

module SimpleUnionImpl refines AbstractSimpleUnionOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetUnionEnsuresPublicly(input: GetUnionInput, output: Result<GetUnionOutput, Error>) {
        true
    }
    predicate GetSingleValueUnionEnsuresPublicly(input: GetSingleValueUnionInput, output: Result<GetSingleValueUnionOutput, Error>) {
        true
    }

    method GetUnion ( config: InternalConfig,  input: GetUnionInput )
      returns (output: Result<GetUnionOutput, Error>)
    {
        var res := GetUnionOutput(union := input.union);

        return Success(res);
    }

    method GetSingleValueUnion ( config: InternalConfig,  input: GetSingleValueUnionInput )
      returns (output: Result<GetSingleValueUnionOutput, Error>)
    {
        var res := GetSingleValueUnionOutput(union := input.union);

        return Success(res);
    }
}