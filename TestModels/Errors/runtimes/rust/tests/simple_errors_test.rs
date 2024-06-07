extern crate simple_errors;

mod simple_errors_test {
    use simple_errors::*;
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
    async fn test_always_error() {
        let result = client()
            .always_error()
            .value("TEST_ERROR_VALUE")
            .send()
            .await;
        match result {
            Ok(_x) => assert!(false),
            Err(e) => {
                assert!(true);
                eprintln!("HERE IS THE ALWAYS ERROR  - {} - END OF ERROR\n", e);
            }
        }
    }

    #[tokio::test]
    async fn test_always_native_error() {
        let result = client()
            .always_native_error()
            .value("TEST_SIMPLE_STRING_KNOWN_VALUE")
            .send()
            .await;
        match result {
            Ok(_x) => assert!(false),
            Err(e) => {
                assert!(true);
                eprintln!("HERE IS THE NATIVE ERROR  - {} - END OF ERROR\n", e);
            }
        }
    }

    #[tokio::test]
    async fn test_always_multiple_errors() {
        let result = client()
            .always_multiple_errors()
            .value("TEST_MULTIPLE_STRING")
            .send()
            .await;
            match result {
                Ok(_x) => assert!(false),
                Err(e) => {
                    assert!(true);
                    eprintln!("HERE IS THE MULTIPLE ERROR  - {} - END OF ERROR\n", e);
                }
            }
    }

    pub fn client() -> Client {
        let config = SimpleErrorsConfig::builder().build().unwrap();
        Client::from_conf(config).unwrap()
    }
}
