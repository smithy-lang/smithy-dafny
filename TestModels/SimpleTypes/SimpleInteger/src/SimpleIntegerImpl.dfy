// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleTypesIntegerTypes.dfy"

module SimpleIntegerImpl refines AbstractSimpleTypesIntegerOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetIntegerEnsuresPublicly(input: GetIntegerInput, output: Result<GetIntegerOutput, Error>) {
        true
    }
    predicate GetIntegerKnownValueTestEnsuresPublicly(input: GetIntegerInput, output: Result<GetIntegerOutput, Error>) {
        true
    }
    method GetInteger ( config: InternalConfig,  input: GetIntegerInput )
    returns (output: Result<GetIntegerOutput, Error>) {
        expect input.value.Some?;
        expect (- UInt.INT32_MAX_LIMIT as int32) <= input.value.UnwrapOr(0) <= ((UInt.INT32_MAX_LIMIT - 1) as int32);
        var res := GetIntegerOutput(value := input.value);
        return Success(res);
    }
    method GetIntegerKnownValueTest ( config: InternalConfig,  input: GetIntegerInput )
    returns (output: Result<GetIntegerOutput, Error>) {
        expect input.value.Some?;
        expect input.value.UnwrapOr(0) == 20;
        var res := GetIntegerOutput(value := input.value);
        return Success(res);
    }
}