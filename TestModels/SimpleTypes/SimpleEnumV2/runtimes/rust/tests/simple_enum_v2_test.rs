use simple_enum_v2::types::simple_enum_v2_shape::SimpleEnumV2Shape::*;
use simple_enum_v2::*;

#[tokio::test]
async fn test_get_enum() {
    let result = client().get_enum_v2().value(SECOND).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, SECOND);
}

#[tokio::test]
async fn test_get_first_known_value() {
    let result = client()
        .get_enum_v2_first_known_value_test()
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
        .get_enum_v2_second_known_value_test()
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
        .get_enum_v2_third_known_value_test()
        .value(THIRD)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, THIRD);
}

pub fn client() -> Client {
    let config = SimpleEnumV2Config::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
