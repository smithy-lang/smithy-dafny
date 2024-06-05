use simple_double::*;

#[tokio::test]
async fn test_get_double() {
    let result = client().get_double().value(42f64).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, 42f64);
}

pub fn client() -> Client {
    let config = SimpleDoubleConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
