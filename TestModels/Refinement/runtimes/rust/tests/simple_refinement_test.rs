use simple_refinement::*;
/*
method{:test} Refinement(){
    var client :- expect SimpleRefinement.SimpleRefinement();
    TestGetRefinement(client);
    TestOnlyInput(client);
    TestOnlyOutput(client);
    TestReadonlyOperation(client);
}
*/

/*
method TestGetRefinement(client: ISimpleRefinementClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
{
    var res :- expect client.GetRefinement(GetRefinementInput(requiredString := "GetRefinement", optionalString := Some("GetRefinementOptional")));
    print res;
    expect res.requiredString == "GetRefinement";
    expect res.optionalString.UnwrapOr("") == "GetRefinementOptional";
}
*/
#[tokio::test]
async fn test_get_refinement() {
    let result = client()
        .get_refinement()
        .required_string("GetRefinement")
        .set_optional_string(Some("GetRefinementOptional".to_string()))
        .send()
        .await;

    let output = result.unwrap();
    let required_string = output.required_string();
    let optional_string = output.optional_string().unwrap();

    assert_eq!(required_string, "GetRefinement");
    assert_eq!(optional_string, "GetRefinementOptional");
}

/*
method TestOnlyInput(client: ISimpleRefinementClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
{
    var res :- expect client.OnlyInput(OnlyInputInput(value := Some("InputValue")));
    print res;
}
*/
#[tokio::test]
async fn test_only_input() {
    let result = client().only_input().value("InputValue").send().await;
    assert!(result.is_ok());
}

/*
method TestOnlyOutput(client: ISimpleRefinementClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
{
    var res :- expect client.OnlyOutput();
    print res;
    expect res.value.UnwrapOr("") == "Hello World";
}
*/
#[tokio::test]
async fn test_only_output() {
    let result = client().only_output().send().await;
    let output = result.unwrap();
    let value = output.value().unwrap();
    assert_eq!(value, "Hello World");
}

/*
method TestReadonlyOperation(client: ISimpleRefinementClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
{
    var res :- expect client.ReadonlyOperation(ReadonlyOperationInput(requiredString := "Readonly", optionalString := Some("ReadonlyOptional")));
    print res;
    expect res.requiredString == "Readonly";
    expect res.optionalString.UnwrapOr("") == "ReadonlyOptional";
}
*/
#[tokio::test]
async fn test_readonly_operation() {
    let result = client()
        .readonly_operation()
        .required_string("ReadOnly")
        .optional_string("ReadonlyOptional")
        .send()
        .await;
    let output = result.unwrap();
    assert_eq!(output.required_string(), "ReadOnly");
    assert_eq!(output.optional_string().unwrap(), "ReadonlyOptional");
}

pub fn client() -> Client {
    let config = SimpleRefinementConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
