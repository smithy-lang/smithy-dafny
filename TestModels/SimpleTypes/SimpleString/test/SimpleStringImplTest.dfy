// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesSmithyStringTypes
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
        // utf8EncodedString holds a value of UTF-8 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf8EncodedString := "\u0905\u0928\u093e\u0930";
        var ret :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some(utf8EncodedString)));
        expect ret.value.UnwrapOr("") == utf8EncodedString;
        print ret;
    }
}
