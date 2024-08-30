use simple_union::*;
// method{:test} TestUnion(){
//     var client :- expect SimpleUnion.SimpleUnion();
//     TestMyUnionInteger(client);
//     TestMyUnionString(client);
//     TestKnownValueUnionString(client);
// }

// method TestMyUnionInteger(client: ISimpleUnionClient)
//     requires client.ValidState()
//     modifies client.Modifies
//     ensures client.ValidState()
// {
//     var ret :- expect client.GetUnion(GetUnionInput(union := Some(IntegerValue(100))));

//     expect ret.union.Some?;
//     expect ret.union.value.IntegerValue?;
//     expect ret.union.value.IntegerValue == 100;
//     expect ret.union.value.StringValue? == false;
// }

#[tokio::test]
async fn test_myunion_integer() {
    let result = client()
        .get_union()
        .union(crate::types::MyUnion::IntegerValue(100))
        .send()
        .await;
    let output = result.unwrap();
    let value = output.union().as_ref().unwrap();

    match value {
        crate::types::MyUnion::IntegerValue(n) => assert_eq!(*n, 100),
        _ => panic!("unexpected variant"),
    }
}

// method TestMyUnionString(client: ISimpleUnionClient)
//     requires client.ValidState()
//     modifies client.Modifies
//     ensures client.ValidState()
// {
//     var ret :- expect client.GetUnion(GetUnionInput(union := Some(StringValue("TestString"))));

//     expect ret.union.Some?;
//     expect ret.union.value.StringValue?;
//     expect ret.union.value.StringValue == "TestString";
//     expect ret.union.value.IntegerValue? == false;
// }

#[tokio::test]
async fn test_myunion_string() {
    let result = client()
        .get_union()
        .union(crate::types::MyUnion::StringValue(
            "TestString".to_string(),
        ))
        .send()
        .await;
    let output = result.unwrap();
    let value = output.union().as_ref().unwrap();

    match value {
        crate::types::MyUnion::StringValue(s) => assert_eq!(s, "TestString"),
        _ => panic!("unexpected variant"),
    }
}

// method TestKnownValueUnionString(client: ISimpleUnionClient)
//     requires client.ValidState()
//     modifies client.Modifies
//     ensures client.ValidState()
// {
//     var ret :- expect client.GetKnownValueUnion(GetKnownValueUnionInput(union := Some(Value(10))));

//     expect ret.union.Some?;
//     expect ret.union.value.Value?;
//     expect ret.union.value.Value == 10;
// }

#[tokio::test]
async fn test_known_value_union_string() {
    let result = client()
        .get_known_value_union()
        .union(crate::types::KnownValueUnion::Value(10))
        .send()
        .await;
    let output = result.unwrap();
    let value = output.union().as_ref().unwrap();

    match value {
        crate::types::KnownValueUnion::Value(n) => assert_eq!(*n, 10),
        _ => panic!("unexpected variant"),
    }
}

pub fn client() -> Client {
    let config = SimpleUnionConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
