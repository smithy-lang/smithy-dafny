// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternV2Types.dfy"
include "ExternV2Constructor.dfy"

replaceable module SimpleExternV2Impl refines AbstractSimpleDafnyExternV2Operations  {
    import opened ExternV2Constructor
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetExternV2EnsuresPublicly(input: GetExternV2Input, output: Result<GetExternV2Output, Error>) {
        true
    }
    predicate UseClassExternV2EnsuresPublicly(input: UseClassExternV2Input, output: Result<UseClassExternV2Output, Error>) {
        true
    }
    predicate ExternV2MustErrorEnsuresPublicly(input: ExternV2MustErrorInput, output: Result<ExternV2MustErrorOutput, Error>) {
        true
    }
    method{:extern "GetExternV2"} GetExternV2(config: InternalConfig, input: GetExternV2Input)
        returns (output: Result<GetExternV2Output, Error>)

    method{:extern "ExternV2MustError"} ExternV2MustError(config: InternalConfig, input: ExternV2MustErrorInput)
        returns (output: Result<ExternV2MustErrorOutput, Error>)

    method UseClassExternV2(config: InternalConfig, input: UseClassExternV2Input)
        returns (output: Result<UseClassExternV2Output, Error>) {
            var externClassObject :- ExternV2Constructor.ExternV2ConstructorClass.Build(input:= input.value.UnwrapOr("Error"));
            var res :- externClassObject.GetValue();
            return Success(UseClassExternV2Output(value:=Some(res)));
        }
}
