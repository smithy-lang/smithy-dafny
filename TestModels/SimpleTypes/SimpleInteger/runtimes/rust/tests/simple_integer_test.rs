use simple_integer::*;

#[tokio::test]
async fn test_get_integer() {
    let result = client().get_integer().value(42).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 42);
}

#[tokio::test]
async fn test_get_known_value() {
    let result = client().get_integer_known_value_test().value(20).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 20);
}

pub fn client() -> Client {
    let config = SimpleIntegerConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
