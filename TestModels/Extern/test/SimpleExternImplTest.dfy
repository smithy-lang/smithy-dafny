// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleExternImplTest {
    import SimpleExtern
    import StandardLibrary.UInt
    import opened SimpleDafnyExternTypes
    import opened Wrappers

    method{:test} Externs(){
        var client :- expect SimpleExtern.SimpleExtern();
        TestGetExtern(client);
        TestExternMustError(client);
        TestUseClassExternSuccess(client);
        TestUseClassExternFailure(client);
    }

    method TestGetExtern(client: ISimpleExternClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret :- expect client.GetExtern(input := GetExternInput(blobValue:= Some([0,0,7]),
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

    method TestExternMustError(client: ISimpleExternClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret := client.ExternMustError(input:= ExternMustErrorInput(value := Some("Error")));

        expect ret.Failure?;
        expect ret.error.Opaque?;
        // There is now way to assert the Opaque object type.
    }

    method TestUseClassExternSuccess(client: ISimpleExternClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret :- expect client.UseClassExtern(input := UseClassExternInput(
            value:= Some("TestStringValue")));
        expect ret.value.UnwrapOr("") == "TestStringValue";
    }

    method TestUseClassExternFailure(client: ISimpleExternClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        //The below line would cause the Build method to retrun error instead of class instance.
        var ret := client.UseClassExtern(input := UseClassExternInput(
            value:= Some("Error")));
        expect ret.Failure?;
        expect ret.error.Opaque?;
    }
}
