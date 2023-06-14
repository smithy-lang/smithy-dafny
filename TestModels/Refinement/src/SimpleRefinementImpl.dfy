// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleRefinementTypes.dfy"

module SimpleRefinementImpl refines AbstractSimpleRefinementOperations {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetRefinementEnsuresPublicly(input: GetRefinementInput, output: Result<GetRefinementOutput, Error>) {
        true
    }
    predicate OnlyInputEnsuresPublicly(input: OnlyInputInput, output: Result<(), Error>) {
        true
    }
    predicate OnlyOutputEnsuresPublicly(output: Result<OnlyOutputOutput, Error>) {
        true
    }
    predicate ReadonlyOperationEnsuresPublicly(input: ReadonlyOperationInput, output: Result<ReadonlyOperationOutput, Error>) {
        true
    }

    method GetRefinement(config: InternalConfig, input: GetRefinementInput )
    returns (output: Result<GetRefinementOutput, Error>) {
        var res := GetRefinementOutput(requiredString := input.requiredString, optionalString := input.optionalString);
        return Success(res);
    }

    method OnlyInput(
        config: InternalConfig,
        input: OnlyInputInput
    ) returns (
        output: Result<(), Error>
    ) {
        print input;
        return Success(());
    }

    method OnlyOutput(
        config: InternalConfig
    ) returns (
        output: Result<OnlyOutputOutput, Error>
    ) {
        var res := OnlyOutputOutput(value := Some("Hello World"));
        return Success(res);
    }

    function method ReadonlyOperation... {
        Success(ReadonlyOperationOutput(requiredString := input.requiredString, optionalString := input.optionalString))
    }
}