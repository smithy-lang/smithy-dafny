extern crate simple_string;

mod simple_string_test {
  use simple_string::*;
  /*
  method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
        TestGetStringSingleValue(client);
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
    let result = client().get_string().value("TEST_SIMPLE_STRING_VALUE").send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, "TEST_SIMPLE_STRING_VALUE");
  }

  #[tokio::test]
  async fn test_get_string_single_value() {
    let result = client().get_string_single_value().value("TEST_SIMPLE_STRING_SINGLE_VALUE").send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, "TEST_SIMPLE_STRING_SINGLE_VALUE");
  }

   /*method TestGetStringUTF8(client: ISimpleTypesStringClient)
    {
        // utf8EncodedString holds a value of UTF-8 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf8EncodedString := "\u0905\u0928\u093e\u0930";
        var ret :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some(utf8EncodedString)));
        expect ret.value.UnwrapOr("") == utf8EncodedString;
        print ret;
    }*/
  #[tokio::test]
  async fn test_get_string_utf8() {
    let utf8_encoded_string = "\u{0905}\u{0928}\u{093e}\u{0930}";
    let result = client().get_string_utf8().value(utf8_encoded_string).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, utf8_encoded_string);
  }

  pub fn client() -> Client {
    let config = Config::builder().build();
    Client::from_conf(config).unwrap()
  }
}