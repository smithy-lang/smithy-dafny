// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsDependencyprojectTypes.dfy"

module SimpleMultiplemodelsDependencyprojectImpl refines AbstractSimpleMultiplemodelsDependencyprojectOperations {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate SomeDependencyOperationEnsuresPublicly(input: SomeDependencyOperationInput, output: Result<SomeDependencyOperationOutput, Error>) {
        true
    }

    method SomeDependencyOperation(config: InternalConfig, input: SomeDependencyOperationInput)
    returns (output: Result<SomeDependencyOperationOutput, Error>) {
        var res := SomeDependencyOperationOutput();
        return Success(res);
    }
}