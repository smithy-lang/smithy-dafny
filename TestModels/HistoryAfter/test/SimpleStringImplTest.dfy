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
        label before:

        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        
        assert history.NewEventSuchThat@before((e: Event) =>
            && e is GetStringEvent
            && var e' := e as GetStringEvent;
            && e'.input.value == Some("TEST_SIMPLE_STRING_VALUE")
            && e'.output == Success(ret));
    }

    method TestMultipleCallsToSameOperation(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();
        label before:
        
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        var ret2 :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")), history);

        assert |history.events| == |old@before(history.events)| + 2;
        
        var last: Event := Last(history.events);
        assert last is GetStringEvent;
        var last' := last as GetStringEvent;
        assert last'.input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert last'.output.value == ret2;

        var secondLast: Event := Last(DropLast(history.events));
        assert secondLast is GetStringEvent;
        var secondLast' := secondLast as GetStringEvent;
        assert secondLast'.input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert secondLast'.output.value == ret;
    }

    method TestMultipleCallsToDifferentOperations(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var history := new History();
        label before:
        
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")), history);
        var ret2 :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE_2")), history);

        assert |history.events| == |old@before(history.events)| + 2;
        
        var last: Event := Last(history.events);
        assert last is GetStringUTF8Event;
        var last' := last as GetStringUTF8Event;
        assert last'.input.value == Some("TEST_SIMPLE_STRING_VALUE_2");
        assert last'.output.value == ret2;

        var secondLast: Event := Last(DropLast(history.events));
        assert secondLast is GetStringEvent;
        var secondLast' := secondLast as GetStringEvent;
        assert secondLast'.input.value == Some("TEST_SIMPLE_STRING_VALUE");
        assert secondLast'.output.value == ret;
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
