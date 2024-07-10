use simple_extendable::operation::create_extendable_resource::*;
use simple_extendable::operation::get_extendable_resource_data::*;
use simple_extendable::types::extendable_resource::ExtendableResourceRef;
use simple_extendable::types::*;
use simple_extendable::*;

const TEST_RESOURCE_NAME: &str = "Dafny-Test";
const DEFAULT_RESOURCE_NAME: &str = "dafny-default";

#[derive(Debug)]
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
    fn always_modeled_error(
        &mut self,
        input: crate::operation::always_modeled_error::AlwaysModeledErrorInput,
    ) -> Result<
        crate::operation::always_modeled_error::AlwaysModeledErrorOutput,
        crate::operation::always_modeled_error::AlwaysModeledErrorError,
    > {
        Err(crate::operation::always_modeled_error::AlwaysModeledErrorError::SimpleExtendableResourcesException(
            crate::error::simple_extendable_resources_exception::SimpleExtendableResourcesException
        {
            message : "Hard Coded Exception in src/dafny".to_string(),
            meta : ::std::default::Default::default()
    }))
    }
}

pub fn DafnyFactory() -> ExtendableResourceRef {
    std::rc::Rc::new(std::cell::RefCell::new(MyResource {}))
}

// Tests the Resource created purely through Dafny Source Code
#[tokio::test]
pub async fn TestClientDafnyResource() {
    let config = SimpleExtendableResourcesConfig::builder().build().unwrap();
    let client = Client::from_conf(config.clone()).unwrap();

    // The explicit type cast is needed for the `is` test on the next line
    let resource = TestCreateExtendableResource(&client, TEST_RESOURCE_NAME).await;
    eprintln!("\nafter TestCreateExtendableResource");
    expect resource is ExtendableResource.ExtendableResource;
    // The `is` test above asserts this a "pure" Dafny resource
    TestNoneUseExtendableResource(&client, resource.clone(), TEST_RESOURCE_NAME);
    eprintln!("\nafter TestNoneUseExtendableResource");
    TestSomeUseExtendableResource(&client, resource.clone(), TEST_RESOURCE_NAME);
    eprintln!("\nafter TestSomeUseExtendableResource");
    TestUseAlwaysModeledError(client, resource);
    TestUseAlwaysMultipleErrors(client, resource);
    TestDafnyUseAlwaysOpaqueError(client, resource);
    eprintln!("\n before drop resource\n");
    drop(resource);
    eprintln!("\n before drop client\n");
    drop(client);
    eprintln!("\n before drop config\n");
    drop(config);
    eprintln!("\n before exit\n");
}

  // Test the Resource created through an Extern
  #[tokio::test]
  pub fn TestClientNativeResource()
  {
    let client = SimpleExtendableResources::builder().build();
    // The explicit type cast is needed for the `is` test on the next line
    var resource: Types.IExtendableResource := DafnyFactory();
    // expect !(resource is ExtendableResource.ExtendableResource);
    // The `is` test above asserts this NOT a "pure" Dafny resource
    assert fresh(resource.Modifies - client.Modifies - {client.History});
    TestNoneUseExtendableResource(client, resource, ExtendableResource.DEFAULT_RESOURCE_NAME);
    TestSomeUseExtendableResource(client, resource, ExtendableResource.DEFAULT_RESOURCE_NAME);
    // TestUseAlwaysModeledError(client, resource);
    // TestUseAlwaysMultipleErrors(client, resource);
    // TestUseAlwaysOpaqueError(client, resource);
  }

pub async fn TestCreateExtendableResource(client: &Client, name: &str) -> ExtendableResourceRef {
    client
        .create_extendable_resource()
        .name(name)
        .send()
        .await
        .unwrap()
        .output()
}

pub async fn TestNoneUseExtendableResource(
    client: &Client,
    resource: ExtendableResourceRef,
    name: &str,
) {
    let dataInput = allNone();
    let useOutput = client
        .use_extendable_resource()
        .resource(resource)
        .input(dataInput)
        .send()
        .await
        .unwrap();

    checkNone(name, useOutput.output());
}

pub async fn TestSomeUseExtendableResource(
    client: &Client,
    resource: ExtendableResourceRef,
    name: &str,
) {
    let dataInput = allSome();
    let useOutput = client
        .use_extendable_resource()
        .resource(resource)
        .input(dataInput)
        .send()
        .await
        .unwrap();

    checkSome(name, useOutput.output());
}

#[tokio::test]
async fn TestNativeResource() {
    let resource: ExtendableResourceRef = DafnyFactory();
    TestSomeGetResourceData(resource.clone()).await;
    TestNoneGetResourceData(resource.clone()).await;
    TestAlwaysModeledError(resource);
    //   TestAlwaysMultipleErrors(resource);
    //   TestAlwaysOpaqueError(resource);
    //   TestNoneAlwaysOpaqueError(resource);
}

fn TestAlwaysModeledError(resource: ExtendableResourceRef) {
    let dataInput = crate::operation::always_modeled_error::AlwaysModeledErrorInput::builder()
        .value("Some".to_string())
        .build()
        .unwrap();

    let dataOutput = resource.borrow_mut().always_modeled_error(dataInput);

    CheckModeledError(dataOutput);
}

fn CheckModeledError(
    errorOutput: Result<
        crate::operation::always_modeled_error::AlwaysModeledErrorOutput,
        crate::operation::always_modeled_error::AlwaysModeledErrorError,
    >,
) {
    assert!(errorOutput.is_err());
    let actualError = errorOutput.unwrap_err();
    match actualError {
        crate::operation::always_modeled_error::AlwaysModeledErrorError::SimpleExtendableResourcesException(e) => {
    assert_eq!(e,
        crate::error::simple_extendable_resources_exception::SimpleExtendableResourcesException {
            message : "Hard Coded Exception in src/dafny".to_string(),
            meta : ::std::default::Default::default()
        }
    );
}
        _ => assert!(false)
    }
}

async fn TestSomeGetResourceData(resource: ExtendableResourceRef) {
    let dataInput = allSome();
    let dataOutput = resource
        .borrow_mut()
        .get_extendable_resource_data(dataInput)
        .unwrap();
    checkSome(DEFAULT_RESOURCE_NAME, &dataOutput);
}

async fn TestNoneGetResourceData(resource: ExtendableResourceRef) {
    let dataInput = allNone();
    let dataOutput = resource
        .borrow_mut()
        .get_extendable_resource_data(dataInput)
        .unwrap();
    checkNone(DEFAULT_RESOURCE_NAME, &dataOutput);
}

pub fn client() -> Client {
    let config = SimpleExtendableResourcesConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}

pub fn allNone() -> GetExtendableResourceDataInput {
    GetExtendableResourceDataInput::builder().build().unwrap()
}

pub fn checkNone(name: &str, output: &GetExtendableResourceDataOutput) {
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

pub fn checkSome(name: &str, output: &GetExtendableResourceDataOutput) {
    assert_eq!(
        Some("Some".to_string() + " " + name),
        *output.string_value()
    );
    assert_eq!(Some(vec![1u8]), *output.blob_value());
    assert_eq!(Some(true), output.boolean_value());
    assert_eq!(Some(1), output.integer_value());
    assert_eq!(Some(1), output.long_value());
}
