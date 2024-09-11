use positional::*;

/*
    method TestClient(client: Types.ISimplePositionalClient)
        requires client.ValidState()
        modifies client.Modifies
    {
        TestGetResource(client);
        TestGetResourcePositional(client);
    }

    method TestGetResource(client: Types.ISimplePositionalClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := Types.GetResourceInput(
            name := "Test"
        );
        var output :- expect client.GetResource(input);
        var resource: Types.ISimpleResource := output.output;
        var getNameOutput :- expect resource.GetName(Types.GetNameInput());
        expect getNameOutput.name == "Test";
    }

    method TestGetResourcePositional(client: Types.ISimplePositionalClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := "TestPositional";
        var resource: Types.ISimpleResource :- expect client.GetResourcePositional(input);
        var getNameOutput :- expect resource.GetName(Types.GetNameInput());
        expect getNameOutput.name == "TestPositional";
    }

    method {:test} TestDefaultConfig() {
        var client :- expect SimplePositional.SimplePositional();
        TestClient(client);
    }
*/

async fn test_client(client: &Client) {
    test_get_resource(client).await;
    test_get_resource_positional(client).await;
}

async fn test_get_resource(client: &Client) {
    let output = client.get_resource().name("Test").send().await;
    let resource = output.unwrap().output.unwrap();
    let get_name_output = resource.get_name().send().await.unwrap();
    assert_eq!(Some("Test"), get_name_output.name().as_deref());
}

async fn test_get_resource_positional(client: &Client) {
    let output = client.get_resource_positional().name("Test").send().await;
    let resource = output.unwrap();
    let get_name_output = resource.get_name().send().await.unwrap();
    assert_eq!(Some("Test"), get_name_output.name().as_deref());
}

#[tokio::test]
async fn test_default_config() {
    let config = SimplePositionalConfig::builder().build().unwrap();
    let client = Client::from_conf(config).unwrap();
    test_client(&client).await;
}
