include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesStringTypes
    import opened Wrappers
    method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
    }

    method TestGetString(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret := client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        expect ret.Success?;
        print ret;
    }
}