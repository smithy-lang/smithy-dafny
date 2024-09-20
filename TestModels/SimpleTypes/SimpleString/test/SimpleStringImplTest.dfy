// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleStringImplTest {
    import SimpleString
    import opened SimpleTypesSmithyStringTypes
    import opened Wrappers
    import UTF8
    method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
        TestGetStringKnownValue(client);
        TestGetStringNonAscii(client);
        TestGetStringUTF8(client);
        TestGetStringUTF8KnownValue(client);
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
    method TestGetStringKnownValue(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetStringKnownValue(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_KNOWN_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_KNOWN_VALUE";
        print ret;
    }
    method TestGetStringNonAscii(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        // utf8EncodedString holds a value of UTF-16 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf16EncodedString := "\u0905\u0928\u093e\u0930";
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some(utf16EncodedString)));
        expect ret.value.UnwrapOr("") == utf16EncodedString;
        print ret;
    }
    method TestGetStringUTF8(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        // utf8EncodedString holds a value of UTF-8 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf16EncodedString := "\u0905\u0928\u093e\u0930";
        var utf8EncodedString: UTF8.ValidUTF8Bytes :- expect UTF8.Encode(utf16EncodedString);
        // Note that the "UTF8" here refers to the use of the @dafnyUTF8Bytes trait,
        // which only changes the Dafny representation of strings.
        // This doesn't affect the other languages, and the signature and behavior of GetStringUTF8
        // in the other native languages should be identical to GetString.
        var ret :- expect client.GetStringUTF8(SimpleString.Types.GetStringUTF8Input(value:= Some(utf8EncodedString)));
        var retUnwrapped :- expect ret.value;
        expect retUnwrapped == utf8EncodedString;
        print ret;
    }
    method TestGetStringUTF8KnownValue(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var encoded: UTF8.ValidUTF8Bytes :- expect UTF8.Encode("Hello");
        var ret :- expect client.GetStringUTF8KnownValue(SimpleString.Types.GetStringUTF8Input(value := Some(encoded)));
        var retUnwrapped :- expect ret.value;
        expect retUnwrapped == encoded;
        print ret;
    }
}
