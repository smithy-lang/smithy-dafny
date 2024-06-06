use simple_enum::types::simple_enum_shape::SimpleEnumShape::*;
use simple_enum::*;

#[tokio::test]
async fn test_get_enum() {
    let result = client().get_enum().value(SECOND).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, SECOND);
}

#[tokio::test]
async fn test_get_first_known_value() {
    let result = client()
        .get_enum_first_known_value()
        .value(FIRST)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, FIRST);
}

#[tokio::test]
async fn test_get_second_known_value() {
    let result = client()
        .get_enum_second_known_value()
        .value(SECOND)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, SECOND);
}

#[tokio::test]
async fn test_get_third_known_value() {
    let result = client()
        .get_enum_third_known_value()
        .value(THIRD)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, THIRD);
}

pub fn client() -> Client {
    let config = SimpleEnumConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
