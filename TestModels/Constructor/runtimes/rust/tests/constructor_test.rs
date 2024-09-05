use constructor::{
    operation::get_constructor::{GetConstructorOutput},
    *,
};
/*
    method{:test} TestGetConstructorWithDefaultConfig(){
        var expectedOutput := GetConstructorOutput(
            internalConfigString:= Some("inputString"),
            blobValue:= Some([0]),
            booleanValue:= Some(false),
            stringValue:= Some(""),
            integerValue:= Some(0),
            longValue:= Some(0)
        );
        var client :- expect SimpleConstructor.SimpleConstructor();
        TestGetConstructor(client, expectedOutput);
    }

    method{:test} TestGetConstructorWithParamConfig()
    {
        var paramConfig := SimpleConstructorConfig(
            blobValue:= Some([0, 0, 7]),
            booleanValue:= Some(true),
            stringValue:= Some("ParamString"),
            integerValue:= Some(7),
            longValue:= Some(7)
        );
        var expectedOutput := GetConstructorOutput(
            internalConfigString:= Some("inputString"),
            blobValue:= paramConfig.blobValue,
            booleanValue:= paramConfig.booleanValue,
            stringValue:= paramConfig.stringValue,
            integerValue:= paramConfig.integerValue,
            longValue:= paramConfig.longValue
        );
        var client :- expect SimpleConstructor.SimpleConstructor(config := paramConfig);
        TestGetConstructor(client, expectedOutput);
    }

*/

/*  method TestGetConstructor(client: ISimpleConstructorClient, expectedOutput: GetConstructorOutput)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := GetConstructorInput(value:=Some("inputString"));
        var ret :- expect client.GetConstructor(input := input);
        expect ret.internalConfigString == expectedOutput.internalConfigString;
        expect ret.blobValue == expectedOutput.blobValue;
        expect ret.booleanValue == expectedOutput.booleanValue;
        expect ret.stringValue == expectedOutput.stringValue;
        expect ret.integerValue == expectedOutput.integerValue;
        expect ret.longValue == expectedOutput.longValue;

    }
} */
#[tokio::test]
async fn test_get_constructor_with_default_config() {
    let config = SimpleConstructorConfig::builder().build().unwrap();
    let client = Client::from_conf(config).unwrap();

    let expected_output = GetConstructorOutput::builder()
        .internal_config_string("inputString".to_string())
        .blob_value(aws_smithy_types::Blob::new(vec![0u8]))
        .boolean_value(true)
        .string_value("".to_string())
        .integer_value(0)
        .long_value(0)
        .build()
        .unwrap();

    test_get_constructor(client, expected_output).await;
}

#[tokio::test]
async fn test_get_constructor_with_param_config() {
    let config = SimpleConstructorConfig::builder()
        .blob_value(aws_smithy_types::Blob::new(vec![0, 0, 7]))
        .boolean_value(true)
        .string_value("ParamString".to_string())
        .integer_value(7)
        .long_value(7)
        .build()
        .unwrap();

    let client = Client::from_conf(config).unwrap();

    let expected_output = GetConstructorOutput::builder()
        .internal_config_string("inputString".to_string())
        .blob_value(aws_smithy_types::Blob::new(vec![0, 0, 7]))
        .boolean_value(true)
        .string_value("ParamString".to_string())
        .integer_value(7)
        .long_value(7)
        .build()
        .unwrap();

    test_get_constructor(client, expected_output).await;
}

async fn test_get_constructor(client: Client, expected_output: GetConstructorOutput) {
    let res = client
        .get_constructor()
        .value("inputString")
        .send()
        .await
        .unwrap();

    assert_eq!(
        res.internal_config_string,
        expected_output.internal_config_string
    );
    assert_eq!(res.blob_value, expected_output.blob_value);
    assert_eq!(res.boolean_value, expected_output.boolean_value);
    assert_eq!(res.string_value, expected_output.string_value);
    assert_eq!(res.integer_value, expected_output.integer_value);
    assert_eq!(res.long_value, expected_output.long_value);
}
