// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/LanguageSpecificLogicTypes.dfy"

replaceable module LanguageSpecificLogicImpl refines AbstractLanguageSpecificLogicOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetRuntimeInformationEnsuresPublicly(output: Result<GetRuntimeInformationOutput, Error>) {
        true
    }
}
