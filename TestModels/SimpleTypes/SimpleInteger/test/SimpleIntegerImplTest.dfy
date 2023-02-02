include "../src/Index.dfy"

module  SimpleIntegerImplTest {
    import SimpleInteger
    import opened SimpleTypesIntegerTypes
    import opened Wrappers
    method{:test} GetInteger(){
        var client :- expect SimpleInteger.SimpleInteger();
        TestGetInteger(client);
        TestGetIntegerKnownValue(client);
    }

    method TestGetInteger(client: ISimpleTypesIntegerClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetInteger(SimpleInteger.Types.GetIntegerInput(value:= Some(1)));
        expect ret.value.UnwrapOr(0) == 1;
        print ret;
    }

    method TestGetIntegerKnownValue(client: ISimpleTypesIntegerClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetIntegerKnownValueTest(SimpleInteger.Types.GetIntegerInput(value:= Some(20)));
        expect ret.value.UnwrapOr(0) == 20;
        print ret;
    }
}