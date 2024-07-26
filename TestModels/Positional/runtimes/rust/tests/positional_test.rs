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

#[tokio::test]
async fn test_client() {
    todo!()
}

#[tokio::test]
async fn test_get_resource() {
    todo!()
}

#[tokio::test]
async fn test_get_resource_positional() {
    todo!()
}

#[tokio::test]
async fn test_default_config() {
    todo!()
}
