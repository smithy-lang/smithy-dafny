#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
extern crate simple_string;

#[cfg(test)]
mod SimpleStringImplTest {
  use simple_string::*;
  /*
  method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
        TestGetStringSingleValue(client);
        TestGetStringUTF8(client);
    }
  */

  #[test]
  fn GetString() {
    let config = Config::builder().build();
    let client = Client::from_conf(config);
    TestGetString(&client);
    TestGetStringSingleValue(&client);
    TestGetStringUTF8(&client);
  }

  /*method TestGetString(client: ISimpleTypesStringClient)
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_VALUE";
        print ret;
    } */
  async fn TestGetString(client: &Client) {
    let result = client.get_string().value("TEST_SIMPLE_STRING_VALUE").send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, "TEST_SIMPLE_STRING_VALUE");
  }

  async fn TestGetStringSingleValue(client: &Client) {
    let result = client.get_string().value("TEST_SIMPLE_STRING_VALUE").send().await;
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
  async fn TestGetStringUTF8(client: &Client) {
    let utf8EncodedString = "\u{0905}\u{0928}\u{093e}\u{0930}";
    let result = client.get_string().value(utf8EncodedString).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, utf8EncodedString);
  }
}