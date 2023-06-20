// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleConstructorTypes.dfy"

module SimpleConstructorImpl refines AbstractSimpleConstructorOperations  {
    datatype Config = Config(
        nameonly blobValue: seq<uint8>,
        nameonly booleanValue : bool,
        nameonly stringValue : string,
        nameonly integerValue : int32,
        nameonly longValue : int64
    )
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetConstructorEnsuresPublicly(input: GetConstructorInput, output: Result<GetConstructorOutput, Error>) {
        true
    }
    method GetConstructor ( config: InternalConfig,  input: GetConstructorInput )
        returns (output: Result<GetConstructorOutput, Error>)
    {  
        var res := GetConstructorOutput(
            internalConfigString:= input.value,
            blobValue:= Some(config.blobValue),
            booleanValue:= Some(config.booleanValue),
            stringValue:= Some(config.stringValue),
            integerValue:= Some(config.integerValue),
            longValue:= Some(config.longValue)
            );
        return Success(res);
    }
}