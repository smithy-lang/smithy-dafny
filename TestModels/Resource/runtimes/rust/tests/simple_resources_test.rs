use simple_resource::SimpleResourceImpl;
use simple_resources::operation::get_resource_data::*;
use simple_resources::types::*;
use simple_resources::*;

#[tokio::test]
async fn TestCustomConfig() {
    TestClient(
        SimpleResourcesConfig::builder()
            .name("Dafny")
            .build()
            .unwrap(),
    )
    .await;
}

async fn TestClient(config: SimpleResourcesConfig) {
    let client = Client::from_conf(config.clone()).unwrap();
    let resource = TestGetResources(client).await;
    TestNoneGetData(config.clone(), resource.clone()).await;
    TestSomeGetData(config.clone(), resource.clone()).await;
}

async fn TestNoneGetData(config: SimpleResourcesConfig, resource: SimpleResourceImpl) {
    let input = allNone();
    let result = resource.borrow_mut().GetResourceData(input).unwrap();
    checkMostNone(config.name().to_string(), result);
}

async fn TestSomeGetData(config: SimpleResourcesConfig, resource: SimpleResourceImpl) {
    let input = allSome();
    let result = resource.borrow_mut().GetResourceData(input).unwrap();
    checkSome(config.name().to_string(), result);
}

async fn TestGetResources(client: Client) -> SimpleResourceImpl {
    let output = client.get_resources().value("Test").send().await.unwrap();
    output.output()
}

pub fn client() -> Client {
    let config = SimpleResourcesConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}

pub fn allNone() -> GetResourceDataInput {
    GetResourceDataInput::builder().build().unwrap()
}

pub fn checkMostNone(name: String, output: GetResourceDataOutput) {
    assert_eq!(Some(name), *output.string_value());
    assert_eq!(None, *output.blob_value());
    assert_eq!(None, output.boolean_value());
    assert_eq!(None, output.integer_value());
    assert_eq!(None, output.long_value());
}

pub fn allSome() -> GetResourceDataInput {
    GetResourceDataInput::builder()
        .blob_value(vec![1u8])
        .boolean_value(true)
        .string_value("Some".to_string())
        .integer_value(1)
        .long_value(1)
        .build()
        .unwrap()
}

pub fn checkSome(name: String, output: GetResourceDataOutput) {
    assert_eq!(Some(name + " Some"), *output.string_value());
    assert_eq!(Some(vec![1u8]), *output.blob_value());
    assert_eq!(Some(true), output.boolean_value());
    assert_eq!(Some(1), output.integer_value());
    assert_eq!(Some(1), output.long_value());
}
