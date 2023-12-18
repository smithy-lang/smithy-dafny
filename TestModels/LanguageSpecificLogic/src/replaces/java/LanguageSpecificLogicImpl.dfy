// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyLanguageSpecificLogicTypes.dfy"
include "LanguageSpecificLogicConstructor.dfy"

module LanguageSpecificLogicImpl refines AbstractSimpleDafnyLanguageSpecificLogicOperations  {
    import opened LanguageSpecificLogicConstructor
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetLanguageSpecificLogicEnsuresPublicly(input: GetLanguageSpecificLogicInput, output: Result<GetLanguageSpecificLogicOutput, Error>) {
        true
    }
    predicate UseClassLanguageSpecificLogicEnsuresPublicly(input: UseClassLanguageSpecificLogicInput, output: Result<UseClassLanguageSpecificLogicOutput, Error>) {
        true
    }
    predicate LanguageSpecificLogicMustErrorEnsuresPublicly(input: LanguageSpecificLogicMustErrorInput, output: Result<LanguageSpecificLogicMustErrorOutput, Error>) {
        true
    }
    // This method is listed as an operation on the service in the Smithy model.
    // Smithy-Dafny will write code to call this operation.
    method AllRuntimesMethod(config: InternalConfig, input: AllRuntimesMethodInput)
        returns (output: Result<AllRuntimesMethodOutput, Error>)
        ensures output.Success? ==> output.value != ""
    {
        return PerLanguageExternMethod(config, input);
    }

    // This method is NOT listed as an operation on the service in the Smithy model.
    // Since this is an extern method with a different name per language, we can't define
    //   the interface for this method on the Smithy model.
    // Instead, we define the `AllRuntimesMethod` which IS a Smithy operation
    //   and call this method from there.
    method PerLanguageExternMethod(config: InternalConfig, input: AllRuntimesMethodInput)
            returns (output: Result<AllRuntimesMethodOutput, Error>)
            ensures output.Success? ==> output.value != ""
}
