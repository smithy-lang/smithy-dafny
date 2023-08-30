// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesSmithyStringTypes
    import opened Wrappers
    method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestSingleCall(client);
    }

    method TestSingleCall(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        
        assert |client.History.GetString| == |old(client.History.GetString)| + 1;
        assert Last(client.History.GetString).input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert Last(client.History.GetString).output.value == ret;
    }

    method TestMultipleCallsToSameOperation(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        var ret2 :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")));

        assert |client.History.GetString| == |old(client.History.GetString)| + 2;
        assert Last(client.History.GetString).input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert Last(client.History.GetString).output.value == ret2;
        assert Last(DropLast(client.History.GetString)).input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert Last(DropLast(client.History.GetString)).output.value == ret;
    }

    method TestMultipleCallsToDifferentOperations(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        var ret2 :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")));

        assert |client.History.GetString| == |old(client.History.GetString)| + 1;
        assert Last(client.History.GetString).input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert Last(client.History.GetString).output.value == ret;

        assert |client.History.GetStringUTF8| == |old(client.History.GetStringUTF8)| + 1;
        assert Last(client.History.GetStringUTF8).input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert Last(client.History.GetStringUTF8).output.value == ret2;

        // Not possible to express that the call to GetString occurred before the call to GetStringUTF8
    }
    
    // Normally from Seq.dfy in dafny-lang/libraries:

    function DropLast<T>(s: seq<T>): seq<T>
        requires 0 < |s|
    {
        s[..(|s| - 1)]
    }

    function Last<T>(s: seq<T>): T 
        requires 0 < |s|
    {
        s[|s| - 1]
    }
}
