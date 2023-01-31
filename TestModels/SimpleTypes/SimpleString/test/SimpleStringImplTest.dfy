include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesStringTypes
    import opened Wrappers
    method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
        TestGetStringSingleValue(client);
        TestGetStringUTF8(client);
    }

    method TestGetString(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_VALUE";
        print ret;
    }
    method TestGetStringSingleValue(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetStringSingleValue(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_SINGLE_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_SINGLE_VALUE";
        print ret;
    }
    method TestGetStringUTF8(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        // a = TEST_SIMPLE_STRING_UTF8_VALUE
        var a := "\u0054\u0045\u0053\u0054\u005f\u0053\u0049\u004d\u0050\u004c\u0045\u005f\u0053\u0054\u0052\u0049\u004e\u0047\u005f\u0055\u0054\u0046\u0038\u005f\u0056\u0041\u004c\u0055\u0045";
        var ret :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some(a)));
        expect ret.value.UnwrapOr("") == a;
        print ret;
    }
}