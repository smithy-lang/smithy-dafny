// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleConstructorImpl.dfy"
include "SimpleConstructorImplTest.dfy"

module WrappedSimpleConstructorTest {
    import WrappedSimpleConstructorService
    import opened SimpleConstructorTypes
    import SimpleConstructorImplTest
    import opened Wrappers
    
    method{:test} TestGetConstructorWithParamConfig() {
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
        var client :- expect WrappedSimpleConstructorService.WrappedSimpleConstructor(config := paramConfig);
        SimpleConstructorImplTest.TestGetConstructor(client, expectedOutput);
    }

    method{:test} TestGetConstructorWithDefaultConfig() {
        var expectedOutput := GetConstructorOutput(
            internalConfigString:= Some("inputString"),
            blobValue:= Some([0]),
            booleanValue:= Some(false),
            stringValue:= Some(""),
            integerValue:= Some(0),
            longValue:= Some(0)
        );
        var client :- expect WrappedSimpleConstructorService.WrappedSimpleConstructor();
        SimpleConstructorImplTest.TestGetConstructor(client, expectedOutput);
    }
}