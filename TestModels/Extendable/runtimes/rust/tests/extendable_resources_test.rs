use simple_extendable::operation::get_extendable_resource_data::*;
use simple_extendable::types::extendable_resource::ExtendableResourceRef;
use simple_extendable::types::*;
use simple_extendable::*;

// const TEST_RESOURCE_NAME : &str = "Dafny-Test";
const DEFAULT_RESOURCE_NAME: &str = "dafny-default";

struct MyResource {}
impl ExtendableResource for MyResource {
    fn get_extendable_resource_data(
        &mut self,
        input: simple_extendable::operation::get_extendable_resource_data::GetExtendableResourceDataInput,
    ) -> Result<
        simple_extendable::operation::get_extendable_resource_data::GetExtendableResourceDataOutput,
        GetExtendableResourceDataError,
    > {
        let rtnString: String = match input.string_value() {
            None => DEFAULT_RESOURCE_NAME.to_string(),
            Some(x) => x.to_string() + " " + DEFAULT_RESOURCE_NAME,
        };

        Ok(simple_extendable::operation::get_extendable_resource_data::GetExtendableResourceDataOutput
            ::builder()
            .set_blob_value(input.blob_value().clone())
            .set_boolean_value(input.boolean_value())
            .set_integer_value(input.integer_value())
            .set_long_value(input.long_value())
            .set_string_value(Some(rtnString))
            .build()
            .unwrap()
        )
    }
}

pub fn DafnyFactory() -> ExtendableResourceRef {
    std::rc::Rc::new(std::cell::RefCell::new(MyResource {}))
}

#[tokio::test]
async fn TestNativeResource() {
    let resource: ExtendableResourceRef = DafnyFactory();
    TestSomeGetResourceData(resource.clone()).await;
    TestNoneGetResourceData(resource.clone()).await;
    //   TestAlwaysModeledError(resource);
    //   TestAlwaysMultipleErrors(resource);
    //   TestAlwaysOpaqueError(resource);
    //   TestNoneAlwaysOpaqueError(resource);
}

async fn TestSomeGetResourceData(resource: ExtendableResourceRef) {
    let dataInput = allSome();
    let dataOutput = resource
        .borrow_mut()
        .get_extendable_resource_data(dataInput)
        .unwrap();
    checkSome(DEFAULT_RESOURCE_NAME, dataOutput);
}

async fn TestNoneGetResourceData(resource: ExtendableResourceRef) {
    let dataInput = allNone();
    let dataOutput = resource
        .borrow_mut()
        .get_extendable_resource_data(dataInput)
        .unwrap();
    checkNone(DEFAULT_RESOURCE_NAME, dataOutput);
}

pub fn client() -> Client {
    let config = SimpleExtendableResourcesConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}

pub fn allNone() -> GetExtendableResourceDataInput {
    GetExtendableResourceDataInput::builder().build().unwrap()
}

pub fn checkNone(name: &str, output: GetExtendableResourceDataOutput) {
    assert_eq!(Some(name.to_string()), *output.string_value());
    assert_eq!(None, *output.blob_value());
    assert_eq!(None, output.boolean_value());
    assert_eq!(None, output.integer_value());
    assert_eq!(None, output.long_value());
}

pub fn allSome() -> GetExtendableResourceDataInput {
    GetExtendableResourceDataInput::builder()
        .blob_value(vec![1u8])
        .boolean_value(true)
        .string_value("Some".to_string())
        .integer_value(1)
        .long_value(1)
        .build()
        .unwrap()
}

pub fn checkSome(name: &str, output: GetExtendableResourceDataOutput) {
    assert_eq!(
        Some("Some".to_string() + " " + name),
        *output.string_value()
    );
    assert_eq!(Some(vec![1u8]), *output.blob_value());
    assert_eq!(Some(true), output.boolean_value());
    assert_eq!(Some(1), output.integer_value());
    assert_eq!(Some(1), output.long_value());
}
