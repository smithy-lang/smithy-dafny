use simple_long::*;

#[tokio::test]
async fn test_get_long() {
    let result = client().get_long().value(42i64).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 42i64);
}

#[tokio::test]
async fn test_get_known_value() {
    let result = client().get_long_known_value().value(33i64).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 33i64);
}

pub fn client() -> Client {
    let config = Config::builder().build();
    Client::from_conf(config).unwrap()
}
