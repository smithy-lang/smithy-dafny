// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleAggregateTypes.dfy"

module SimpleAggregateImpl refines AbstractSimpleAggregateOperations {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>) {
        true
    }
    predicate GetAggregateKnownValueTestEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>) {
        true
    }
    method GetAggregate(config: InternalConfig, input: GetAggregateInput )
    returns (output: Result<GetAggregateOutput, Error>) {
        var res := GetAggregateOutput(recursiveUnion := input.recursiveUnion);
        return Success(res);
    }

    // This method is only used for known-value testing. See "Known Value Tests" inside TestModels' README file.
    method GetAggregateKnownValueTest(config: InternalConfig, input: GetAggregateInput )
    returns (output: Result<GetAggregateOutput, Error>) {
        ValidateInput(input);
        var res := GetAggregateOutput(recursiveUnion := input.recursiveUnion);
        return Success(res);
    }

    method ValidateInput(input: GetAggregateInput) {
        
    }
}