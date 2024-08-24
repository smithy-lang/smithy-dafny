use simple_enum::types::SimpleEnumShape::*;
use simple_enum::*;

#[tokio::test]
async fn test_get_enum() {
    let result = client().get_enum().value(Second).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, Second);
}

#[tokio::test]
async fn test_get_first_known_value() {
    let result = client()
        .get_enum_first_known_value_test()
        .value(First)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, First);
}

#[tokio::test]
async fn test_get_second_known_value() {
    let result = client()
        .get_enum_second_known_value_test()
        .value(Second)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, Second);
}

#[tokio::test]
async fn test_get_third_known_value() {
    let result = client()
        .get_enum_third_known_value_test()
        .value(Third)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, Third);
}

pub fn client() -> Client {
    let config = SimpleEnumConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
