// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesSmithyStringTypes.dfy"

module SimpleStringImpl refines AbstractSimpleTypesSmithyStringOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringKnownValueEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringUTF8EnsuresPublicly(input: GetStringUTF8Input, output: Result<GetStringUTF8Output, Error>) {
        true
    }
    predicate GetStringUTF8KnownValueEnsuresPublicly(input: GetStringUTF8Input, output: Result<GetStringUTF8Output, Error>) {
        true
    }
    method GetString ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringKnownValue ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        expect input.value.Some?;
        expect input.value.value == "TEST_SIMPLE_STRING_KNOWN_VALUE"; // This is done so as to assert that polymorph layer is doing one way conversion right as well.
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringUTF8 ( config: InternalConfig,  input: GetStringUTF8Input )
    returns (output: Result<GetStringUTF8Output, Error>) {
        expect input.value.Some?;
        var res := GetStringUTF8Output(value := input.value);
        return Success(res);
    }
    method GetStringUTF8KnownValue ( config: InternalConfig,  input: GetStringUTF8Input )
    returns (output: Result<GetStringUTF8Output, Error>) {
        expect input.value.Some?;
        var expected := [0x48, 0x65, 0x6C, 0x6C, 0x6F];  // Hello in UTF8
        expect input.value.value == expected; // This is done so as to assert that polymorph layer is doing one way conversion right as well.
        var res := GetStringUTF8Output(value := input.value);
        return Success(res);
    }
}
