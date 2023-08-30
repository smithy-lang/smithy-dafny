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
        
        assert GetStringEvent.WasNthLastWith(history, 0, (e: GetStringEvent) =>
            && e.input.value == Some("TEST_SIMPLE_STRING_VALUE")
            && e.output == Success(ret));
    }

    method TestMultipleCallsToSameOperation(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();
        
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        var ret2 :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")), history);

        assert GetStringEvent.WasNthLastWith(history, 1, (e: GetStringEvent) =>
            && e.input.value == Some("TEST_SIMPLE_STRING_VALUE")
            && e.output == Success(ret));
        assert GetStringEvent.WasNthLastWith(history, 0, (e: GetStringEvent) =>
            && e.input.value == Some("TEST_SIMPLE_STRING_VALUE_2")
            && e.output == Success(ret2));
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
        
        assert GetStringEvent.WasNthLastWith(history, 1, (e: GetStringEvent) =>
            && e.input.value == Some("TEST_SIMPLE_STRING_VALUE")
            && e.output == Success(ret));
        assert GetStringUTF8Event.WasNthLastWith(history, 0, (e: GetStringUTF8Event) =>
            && e.input.value == Some("TEST_SIMPLE_STRING_VALUE_2")
            && e.output == Success(ret2));
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
