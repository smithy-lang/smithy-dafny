use simple_resources::*;
/*
    method{:test} GetResourcesTrue(){
        var client :- expect SimpleResources.SimpleResources();
        TestGetResourcesTrue(client);
    }
    method{:test} GetResourcesFalse(){
        var client :- expect SimpleResources.SimpleResources();
        TestGetResourcesFalse(client);
    }
*/

/*method TestGetResourcesTrue(client: ISimpleTypesResourcesClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetResources(SimpleResources.Types.GetResourcesInput(value:= Some(true)));
        expect ret.value.UnwrapOr(false) == true;
        print ret;
    }
} */
#[tokio::test]
async fn test_get_resources_true() {
    let result = client().get_resources().value(true).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert!(value);
}

/*method TestGetResourcesFalse(client: ISimpleTypesResourcesClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetResources(SimpleResources.Types.GetResourcesInput(value:= Some(false)));
        expect ret.value.UnwrapOr(true) == false;
        print ret;
    }
} */
#[tokio::test]
async fn test_get_resources_false() {
    let result = client().get_resources().value(false).send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert!(!value);
}

pub fn client() -> Client {
    let config = SimpleResourcesConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
