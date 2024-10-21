extern crate simple_string;

mod simple_string_test {
    use simple_string::*;
    /*
    method{:test} GetString(){
          var client :- expect SimpleString.SimpleString();
          TestGetString(client);
          TestGetStringKnownValue(client);
          TestGetStringUTF8(client);
      }
    */

    /*method TestGetString(client: ISimpleTypesStringClient)
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_VALUE";
        print ret;
    } */
    #[tokio::test]
    async fn test_get_string() {
        let result = client()
            .get_string()
            .value("TEST_SIMPLE_STRING_VALUE")
            .send()
            .await;
        let output = result.unwrap();
        let value = output.value().as_ref().unwrap();
        assert_eq!(value, &"TEST_SIMPLE_STRING_VALUE");
    }

    #[tokio::test]
    async fn test_get_string_known_value() {
        let result = client()
            .get_string_known_value()
            .value("TEST_SIMPLE_STRING_KNOWN_VALUE")
            .send()
            .await;
        let output = result.unwrap();
        let value = output.value().as_ref().unwrap();
        assert_eq!(value, &"TEST_SIMPLE_STRING_KNOWN_VALUE");
    }

    /*method TestGetStringNonAscii(client: ISimpleTypesStringClient)
    {
        // utf8EncodedString holds a value of UTF-16 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf16EncodedString := "\u0905\u0928\u093e\u0930";
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some(utf16EncodedString)));
        expect ret.value.UnwrapOr("") == utf16EncodedString;
        print ret;
    }*/
    #[tokio::test]
    async fn test_get_string_nonascii() {
        let utf8_encoded_string = "\u{0905}\u{0928}\u{093e}\u{0930}";
        let result = client()
            .get_string()
            .value(utf8_encoded_string)
            .send()
            .await;
        let output = result.unwrap();
        let value = output.value().as_ref().unwrap();
        assert_eq!(value, &utf8_encoded_string);
    }

    /*method TestGetStringUTF8(client: ISimpleTypesStringClient)
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
    }*/
    #[tokio::test]
    async fn test_get_string_utf8() {
        let utf8_encoded_string = "\u{0905}\u{0928}\u{093e}\u{0930}";
        let result = client()
            .get_string_utf8()
            .value(utf8_encoded_string)
            .send()
            .await;
        let output = result.unwrap();
        let value = output.value().as_ref().unwrap();
        assert_eq!(value, &utf8_encoded_string);
    }

    /*method TestGetStringUTF8KnownValue(client: ISimpleTypesStringClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var encoded: UTF8.ValidUTF8Bytes :- expect UTF8.Encode("Hello");
        var ret :- expect client.GetStringUTF8KnownValue(SimpleString.Types.GetStringUTF8Input(value := Some(encoded)));
        var retUnwrapped :- expect ret.value;
        expect retUnwrapped == encoded;
        print ret;
    }*/
    #[tokio::test]
    async fn test_get_string_utf8_known_value() {
        let result = client()
            .get_string_utf8_known_value()
            .value("Hello")
            .send()
            .await;
        let output = result.unwrap();
        let value = output.value().as_ref().unwrap();
        assert_eq!(value, &"Hello");
    }

    pub fn client() -> Client {
        let config = SimpleStringConfig::builder().build().unwrap();
        Client::from_conf(config).unwrap()
    }
}
