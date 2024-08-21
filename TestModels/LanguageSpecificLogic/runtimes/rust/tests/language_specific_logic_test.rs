use language_specific_logic::*;


#[tokio::test]
async fn test_get_runtime_information() {
    let result = client()
        .get_runtime_information()
        .send()
        .await;
    let output = result.unwrap();
    assert_eq!(output.language(), "Rust");
    assert!(output.runtime().contains(std::env::consts::OS));
    assert!(output.runtime().contains(std::env::consts::ARCH));
}

pub fn client() -> Client {
    let config = LanguageSpecificLogicConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
