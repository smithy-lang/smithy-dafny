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
    predicate GetKnownValueUnionEnsuresPublicly(input: GetKnownValueUnionInput, output: Result<GetKnownValueUnionOutput, Error>) {
        true
    }

    method GetUnion ( config: InternalConfig,  input: GetUnionInput )
      returns (output: Result<GetUnionOutput, Error>)
    {
        var res := GetUnionOutput(union := input.union);

        return Success(res);
    }

    method GetKnownValueUnion ( config: InternalConfig,  input: GetKnownValueUnionInput )
      returns (output: Result<GetKnownValueUnionOutput, Error>)
    {
        var res := GetKnownValueUnionOutput(union := input.union);

        return Success(res);
    }
}
