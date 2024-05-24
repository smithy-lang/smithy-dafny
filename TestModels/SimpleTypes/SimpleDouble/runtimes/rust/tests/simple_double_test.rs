use simple_double::*;

#[tokio::test]
async fn test_get_double() {
    let s = vec![0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8];
    let s2 = s.clone();
    let result = client().get_double().value(s).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, &s2);
}

#[tokio::test]
async fn test_get_known_value() {
    let s = vec![0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7];
    let s2 = s.clone();
    let result = client()
        .get_double_known_value()
        .value(s)
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, &s2);
}

pub fn client() -> Client {
    let config = Config::builder().build();
    Client::from_conf(config).unwrap()
}
