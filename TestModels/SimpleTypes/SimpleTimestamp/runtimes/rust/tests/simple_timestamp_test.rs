use simple_timestamp::*;
/*
method {:test} TestClient(){
    var client :- expect SimpleTimestamp.SimpleTimestamp();

    TestGetTimestamp(client);
}
*/

/*
method TestGetTimestamp(client: ISimpleTypesTimestampClient)
  requires client.ValidState()
  modifies client.Modifies
  ensures client.ValidState()
{
    var dafnyTimestamp := "2024-06-11T12:34:56";
    var ret :- expect client.GetTimestamp(SimpleTimestamp.Types.GetTimestampInput(value:= Some(dafnyTimestamp)));
    expect ret.value == Some(dafnyTimestamp);
    print ret;
}
*/
#[tokio::test]
async fn test_get_timestamp() {
    let ts = aws_smithy_types::DateTime::from_str(
        "2024-06-11T12:34:56Z",
        aws_smithy_types::date_time::Format::DateTime,
    )
    .unwrap();
    let result = client().get_timestamp().value(ts).send().await.unwrap();
    let value = result.value().unwrap();
    assert_eq!(value, ts);
}

pub fn client() -> Client {
    let config = SimpleTimestampConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
