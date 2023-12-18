// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

replaceable module SimpleExternV2ImplTest {
    import SimpleExternV2
    import StandardLibrary.UInt
    import opened SimpleDafnyExternV2Types
    import opened Wrappers

    method{:test} ExternV2Tests(){
        var client :- expect SimpleExternV2.SimpleExternV2();
        TestGetExternV2(client);
        TestExternV2MustError(client);
        TestUseClassExternV2Success(client);
        TestUseClassExternV2Failure(client);
    }

    method TestGetExternV2(client: ISimpleExternV2Client)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret :- expect client.GetExternV2(input := GetExternV2Input(blobValue:= Some([0,0,7]),
            booleanValue:= Some(true),
            stringValue:= Some("TestStringValue"),
            integerValue:= Some(100),
            longValue:= Some(9000)));

        expect ret.blobValue.UnwrapOr([]) == [0,0,7];
        expect ret.booleanValue.UnwrapOr(false) == true;
        expect ret.stringValue.UnwrapOr([]) == "TestStringValue";
        expect ret.integerValue.UnwrapOr(0) == 100;
        expect ret.longValue.UnwrapOr(0) == 9000;
    }

    method TestExternV2MustError(client: ISimpleExternV2Client)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret := client.ExternV2MustError(input:= ExternV2MustErrorInput(value := Some("Error")));

        expect ret.Failure?;
        expect ret.error.Opaque?;
        // There is now way to assert the Opaque object type.
    }

    method TestUseClassExternV2Success(client: ISimpleExternV2Client)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret :- expect client.UseClassExternV2(input := UseClassExternV2Input(
            value:= Some("TestStringValue")));
        expect ret.value.UnwrapOr("") == "TestStringValue";
    }

    method TestUseClassExternV2Failure(client: ISimpleExternV2Client)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        //The below line would cause the Build method to retrun error instead of class instance.
        var ret := client.UseClassExternV2(input := UseClassExternV2Input(
            value:= Some("Error")));
        expect ret.Failure?;
        expect ret.error.Opaque?;
    }
}
