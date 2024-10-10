extern crate simple_errors;

mod simple_errors_test {
    use simple_errors::types::error::Error::*;
    use simple_errors::*;

    #[tokio::test]
    async fn test_always_error() {
        let result = client()
            .always_error()
            .value("TEST_ERROR_VALUE")
            .send()
            .await;
        match result {
            Ok(_x) => assert!(false),
            Err(e) => match e {
                SimpleErrorsException { message } => assert!(message == "TEST_ERROR_VALUE"),
                _ => assert!(false, "always_error did not return SimpleErrorsException"),
            },
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
            Err(e) => match e {
                Opaque { obj , ..} => assert!(obj.0.is_some()),
                _ => assert!(false, "always_native_error did not return Opaque"),
            },
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
            Err(e) => match e {
                CollectionOfErrors { list, message } => {
                    assert!(message == "Something");
                    assert!(
                        list == vec![SimpleErrorsException {
                            message: "TEST_MULTIPLE_STRING".to_string()
                        }]
                    );
                }
                _ => assert!(
                    false,
                    "always_multiple_errors did not return CollectionOfErrors"
                ),
            },
        }
    }

    pub fn client() -> Client {
        let config = SimpleErrorsConfig::builder().build().unwrap();
        Client::from_conf(config).unwrap()
    }
}
