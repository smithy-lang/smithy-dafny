use simple_double::*;

#[tokio::test]
async fn test_get_double() {
    let result = client().get_double().value(42f64).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 42f64);
}

#[tokio::test]
async fn test_get_known_value() {
    let result = client()
        .get_double_known_value()
        .value(33f64)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 33f64);
}

pub fn client() -> Client {
    let config = Config::builder().build();
    Client::from_conf(config).unwrap()
}
