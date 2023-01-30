include "../src/Index.dfy"

module  SimpleBooleanImplTest {
    import SimpleBoolean
    import opened SimpleTypesBooleanTypes
    import opened Wrappers
    method{:test} GetBoolean(){
        var client :- expect SimpleBoolean.SimpleBoolean();
        TestGetBoolean(client);
    }

    method TestGetBoolean(client: ISimpleTypesBooleanClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret := client.GetBoolean(SimpleBoolean.Types.GetBooleanInput(value:= Some(true)));
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(false) == true;
        print ret;
    }
}