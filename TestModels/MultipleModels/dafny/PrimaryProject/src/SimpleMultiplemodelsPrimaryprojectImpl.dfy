// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleMultiplemodelsPrimaryprojectTypes.dfy"
include "../../DependencyProject/Model/SimpleMultiplemodelsDependencyprojectTypes.dfy"

module SimpleMultiplemodelsPrimaryprojectImpl refines AbstractSimpleMultiplemodelsPrimaryprojectOperations {
    import SimpleMultiplemodelsDependencyprojectTypes
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate SomePrimaryOperationEnsuresPublicly(input: SomePrimaryOperationInput, output: Result<SomePrimaryOperationOutput, Error>) {
        true
    }
    predicate SomeDependencyOperationEnsuresPublicly(input: SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationInput, output: Result<SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationOutput, Error>) {
        true
    }

    method SomePrimaryOperation(config: InternalConfig, input: SomePrimaryOperationInput)
    returns (output: Result<SomePrimaryOperationOutput, Error>) {
        var res := SomePrimaryOperationOutput();
        return Success(res);
    }

    method SomeDependencyOperation(config: InternalConfig, input: SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationInput)
    returns (output: Result<SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationOutput, Error>) {
        var res := SimpleMultiplemodelsDependencyprojectTypes.SomeDependencyOperationOutput();
        return Success(res);
    }
}