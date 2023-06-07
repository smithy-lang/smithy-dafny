// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleConstructorImplTest {
    import SimpleConstructor
    import StandardLibrary.UInt
    import opened SimpleConstructorTypes
    import opened Wrappers
    
    method{:test} TestGetConstructorWithDefaultConfig(){
        var expectedOutput := GetConstructorOutput(
            internalConfigString:= Some("inputString"),
            blobValue:= Some([0]),
            booleanValue:= Some(false),
            stringValue:= Some(""),
            integerValue:= Some(0),
            longValue:= Some(0)
        );
        var client :- expect SimpleConstructor.SimpleConstructor();
        TestGetConstructor(client, expectedOutput);
    }

    method{:test} TestGetConstructorWithParamConfig()
    {
        var paramConfig := SimpleConstructorConfig(
            blobValue:= Some([0, 0, 7]),
            booleanValue:= Some(true),
            stringValue:= Some("ParamString"),
            integerValue:= Some(7),
            longValue:= Some(7)
        );
        var expectedOutput := GetConstructorOutput(
            internalConfigString:= Some("inputString"),
            blobValue:= paramConfig.blobValue,
            booleanValue:= paramConfig.booleanValue,
            stringValue:= paramConfig.stringValue,
            integerValue:= paramConfig.integerValue,
            longValue:= paramConfig.longValue
        );
        var client :- expect SimpleConstructor.SimpleConstructor(config := paramConfig);
        TestGetConstructor(client, expectedOutput);
    }

    method TestGetConstructor(client: ISimpleConstructorClient, expectedOutput: GetConstructorOutput)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := GetConstructorInput(value:=Some("inputString"));
        var ret :- expect client.GetConstructor(input := input);
        expect ret.internalConfigString == expectedOutput.internalConfigString;
        expect ret.blobValue == expectedOutput.blobValue;
        expect ret.booleanValue == expectedOutput.booleanValue;
        expect ret.stringValue == expectedOutput.stringValue;
        expect ret.integerValue == expectedOutput.integerValue;
        expect ret.longValue == expectedOutput.longValue;

    }
}