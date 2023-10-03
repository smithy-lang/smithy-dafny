// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesSmithyStringTypes
    import opened Wrappers
    import opened Histories
    method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestSingleCall(client);
        TestMultipleCallsToSameOperation(client);
        TestMultipleCallsToDifferentOperations(client);
    }

    method TestSingleCall(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();

        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        
        var e: GetStringEvent := history.LastEvent();
        assert e.input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert e.output == Success(ret);
    }

    method TestMultipleCallsToSameOperation(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();
        
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        var ret2 :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")), history);

        var e: GetStringEvent := history.NthLastEvent(1);
        assert e.input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert e.output == Success(ret);

        var e2: GetStringEvent := history.NthLastEvent(0);
        assert e2.input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert e2.output == Success(ret2);
    }

    method TestMultipleCallsToDifferentOperations(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();
        
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        var ret2 :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")), history);

        assert |history.events| == 2;
        
        var e: GetStringEvent := history.NthLastEvent(1);
        assert e.input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert e.output == Success(ret);
        var e2: GetStringUTF8Event := history.LastEvent();
        assert e2.input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert e2.output == Success(ret2);
    }

    // method GetLongerString(client: ISimpleTypesStringClient, history: History) returns (longerString: Result<string, string>)

    // {
    //     var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("One")), history);
    //     var ret2 :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some("Two")), history);

    // }
    
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
