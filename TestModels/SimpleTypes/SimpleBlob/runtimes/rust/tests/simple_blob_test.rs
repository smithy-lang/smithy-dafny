use simple_blob::*;

/*
        method{:test} GetBlob(){
        var client :- expect SimpleBlob.SimpleBlob();
        TestGetBlob(client);
        TestGetBlobKnownValueTest(client);
    }
*/

/*
   method TestGetBlob(client: ISimpleTypesBlobClient)
     requires client.ValidState()
     modifies client.Modifies
     ensures client.ValidState()
   {
       var s: seq<UInt.uint8> := [0x0, 0x1, 0x2];
       var convertedBlobInput: GetBlobInput := SimpleBlob.Types.GetBlobInput(value:= Some(s));
       SimpleBlobImpl.ValidateBlobType(convertedBlobInput.value.value);
       // Validate values of convertedBlobInput are same as input values
       expect convertedBlobInput.value.value == s;

       var ret :- expect client.GetBlob(convertedBlobInput);

       // Expect output of GetBlob has same value as input sequence
       // i.e. GetBlob(GetBlobInput(seq)) == GetBlobInput(seq)
       expect ret.value.UnwrapOr([0x0]) == convertedBlobInput.value.value;
       // From above, GetBlobInput(seq) value == seq, so the below should be redundant
       expect ret.value.UnwrapOr([0x0]) == s;
       print ret;
   }
*/
#[tokio::test]
async fn test_get_blob() {
    let s = aws_smithy_types::Blob::new(vec![0x0, 0x1, 0x2]);
    let result = client().get_blob().value(s.clone()).send().await;
    let output = result.unwrap();
    let value = output.value().as_ref().unwrap();
    assert_eq!(value, &s);
}

/*
   method TestGetBlobKnownValueTest(client: ISimpleTypesBlobClient)
     requires client.ValidState()
     modifies client.Modifies
     ensures client.ValidState()
   {
       var s: seq<UInt.uint8> := [0x0, 0x2, 0x4];
       var convertedBlobInput: GetBlobInput := SimpleBlob.Types.GetBlobInput(value:= Some(s));
       SimpleBlobImpl.ValidateBlobType(convertedBlobInput.value.value);
       // Validate values of convertedBlobInput are same as input values
       expect convertedBlobInput.value.value == s;

       var ret :- expect client.GetBlobKnownValueTest(convertedBlobInput);

       // Expect output of GetBlob has same value as input sequence
       // i.e. GetBlob(GetBlobInput(seq)) == GetBlobInput(seq)
       expect ret.value.UnwrapOr([0x0]) == convertedBlobInput.value.value;
       // From above, GetBlobInput(seq) value == seq, so the below should be redundant
       expect ret.value.UnwrapOr([0x0]) == s;
       print ret;
   }
*/

#[tokio::test]
async fn test_get_known_value() {
    let s = aws_smithy_types::Blob::new(vec![0x0, 0x2, 0x4]);
    let result = client()
        .get_blob_known_value_test()
        .value(s.clone())
        .send()
        .await;
    let output = result.unwrap();
    let value = output.value().as_ref().unwrap();
    assert_eq!(value, &s);
}

pub fn client() -> Client {
    let config = SimpleBlobConfig::builder().build().unwrap();
    Client::from_conf(config).unwrap()
}
