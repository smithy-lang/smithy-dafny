// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternTypes.dfy"
include "ExternConstructor.dfy"

module SimpleExternImpl refines AbstractSimpleDafnyExternOperations  {
    import opened ExternConstructor
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetExternEnsuresPublicly(input: GetExternInput, output: Result<GetExternOutput, Error>) {
        true
    }
    predicate UseClassExternEnsuresPublicly(input: UseClassExternInput, output: Result<UseClassExternOutput, Error>) {
        true
    }
    predicate ExternMustErrorEnsuresPublicly(input: ExternMustErrorInput, output: Result<ExternMustErrorOutput, Error>) {
        true
    }
    method{:extern "GetExtern"} GetExtern(config: InternalConfig, input: GetExternInput)
        returns (output: Result<GetExternOutput, Error>)

    method{:extern "ExternMustError"} ExternMustError(config: InternalConfig, input: ExternMustErrorInput)
        returns (output: Result<ExternMustErrorOutput, Error>)

    method UseClassExtern(config: InternalConfig, input: UseClassExternInput)
        returns (output: Result<UseClassExternOutput, Error>) {
            var externClassObject :- ExternConstructor.ExternConstructorClass.Build(input:= input.value.UnwrapOr("Error"));
            var res :- externClassObject.GetValue();
            return Success(UseClassExternOutput(value:=Some(res)));
        }
}
