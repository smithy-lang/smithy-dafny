// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleCallingawssdkfromlocalserviceImpl.dfy"

module SimpleCallingawssdkfromlocalserviceImplTest {
  import Com.Amazonaws.Dynamodb
  import Com.Amazonaws.Kms
  import SimpleCallingawssdkfromlocalservice
  import opened StandardLibrary.UInt

  // For call to DDB
  const TABLE_ARN_SUCCESS_CASE := "arn:aws:dynamodb:us-west-2:370957321024:table/TestTable"
  const TABLE_ARN_FAILURE_CASE := "arn:aws:dynamodb:us-west-2:370957321024:table/TestTableFailure"

  // For call to KMS
  const KEY_ID_SUCCESS_CASE := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
  const KEY_ID_FAILURE_CASE := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g"
  // The string "asdf" as bytes
  const PLAIN_TEXT: Kms.Types.PlaintextType := [ 97, 115, 100, 102 ]

  // This is required because
  // https://github.com/dafny-lang/dafny/issues/2311
  function method workAround(literal: seq<uint8>)
    :(ret: Kms.Types.CiphertextType)
    requires Kms.Types.IsValid_CiphertextType(literal)
  {literal}

  import opened SimpleCallingawssdkfromlocalserviceTypes
  import opened Wrappers
  method{:test} CallDDBScan(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallDDBScan_Success(client);
    TestCallDDBScan_Failure(client);
  }

  method TestCallDDBScan_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resSuccess := client.CallDDBScan(SimpleCallingawssdkfromlocalservice.Types.CallDDBScanInput(ddbClient := Some(ddbClient), tableArn := TABLE_ARN_SUCCESS_CASE));

    expect resSuccess.Success?;
    expect resSuccess.value.itemOutput.Some?;
  }

  method TestCallDDBScan_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resFailure := client.CallDDBScan(SimpleCallingawssdkfromlocalservice.Types.CallDDBScanInput(ddbClient := Some(ddbClient), tableArn := TABLE_ARN_FAILURE_CASE));

    expect resFailure.Failure?;
    expect resFailure.error.ComAmazonawsDynamodb?;
    expect resFailure.error.ComAmazonawsDynamodb.OpaqueWithText?;
  }

  method{:test} CallDDBGetItem(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallDDBGetItem_Success(client);
    TestCallDDBGetItem_Failure(client);
  }

  method TestCallDDBGetItem_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var Key2Get: Dynamodb.Types.Key := map[
      "branch-key-id" := Dynamodb.Types.AttributeValue.S("aws-kms-h"),
      "version" := Dynamodb.Types.AttributeValue.S("1")
    ];
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resSuccess := client.CallDDBGetItem(SimpleCallingawssdkfromlocalservice.Types.CallDDBGetItemInput(ddbClient := ddbClient, tableArn := TABLE_ARN_SUCCESS_CASE, key := Key2Get));

    expect resSuccess.Success?;
    expect resSuccess.value.itemOutput.Some?;
    var output := resSuccess.value.itemOutput.value;

    expect output.Keys == {"branch-key-id", "version", "create-time", "enc", "hierarchy-version", "status"};
    expect |output.Keys| == |output.Values|;
  }

  method TestCallDDBGetItem_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var Key2Get: Dynamodb.Types.Key := map[
      "wrong-data" := Dynamodb.Types.AttributeValue.S("aws-kms-h"),
      "version" := Dynamodb.Types.AttributeValue.S("1")
    ];
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resFailure := client.CallDDBGetItem(SimpleCallingawssdkfromlocalservice.Types.CallDDBGetItemInput(ddbClient := ddbClient, tableArn := TABLE_ARN_FAILURE_CASE, key := Key2Get));

    expect resFailure.Failure?;
    expect resFailure.error.ComAmazonawsDynamodb?;
    expect resFailure.error.ComAmazonawsDynamodb.OpaqueWithText?;
  }

  method{:test} CallDDBPutItem(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallDDBPutItem_Success(client);
    TestCallDDBPutItem_Failure(client);
  }

  method TestCallDDBPutItem_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var attributeValueMap: Dynamodb.Types.PutItemInputAttributeMap := map[
      "branch-key-id"   := Dynamodb.Types.AttributeValue.S("aws-kms-put-item"),
      "status" := Dynamodb.Types.AttributeValue.S("ACTIVE"),
      "version" := Dynamodb.Types.AttributeValue.S("version-1")
    ];
    var conditionExpression: Dynamodb.Types.ConditionExpression :=  "attribute_exists(version)";
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resSuccess := client.CallDDBPutItem(SimpleCallingawssdkfromlocalservice.Types.CallDDBPutItemInput(ddbClient := ddbClient, tableArn := TABLE_ARN_SUCCESS_CASE, attributeMap := attributeValueMap, conditionExpression := conditionExpression));

    expect resSuccess.Success?;
  }

  method TestCallDDBPutItem_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var attributeValueMap: Dynamodb.Types.PutItemInputAttributeMap := map[
      "branch-key-id"   := Dynamodb.Types.AttributeValue.S("aws-kms-put-item"),
      "status" := Dynamodb.Types.AttributeValue.S("ACTIVE"),
      "version" := Dynamodb.Types.AttributeValue.S("version-1")
    ];
    var conditionExpression: Dynamodb.Types.ConditionExpression :=  "attribute_not_exists(version)";
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resFailure := client.CallDDBPutItem(SimpleCallingawssdkfromlocalservice.Types.CallDDBPutItemInput(ddbClient := ddbClient, tableArn := TABLE_ARN_SUCCESS_CASE, attributeMap := attributeValueMap, conditionExpression := conditionExpression));

    expect resFailure.Failure?;
    expect resFailure.error.ComAmazonawsDynamodb?;
    expect resFailure.error.ComAmazonawsDynamodb.ConditionalCheckFailedException?;
  }

  method{:test} CallKMSEncrypt(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallKMSEncrypt_Success(client);
    TestCallKMSEncrypt_Failure(client);
  }

  method TestCallKMSEncrypt_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    var resSuccess := client.CallKMSEncrypt(SimpleCallingawssdkfromlocalservice.Types.CallKMSEncryptInput(kmsClient := kmsClient, keyId := KEY_ID_SUCCESS_CASE, plaintext := PLAIN_TEXT));

    expect resSuccess.Success?;
    expect resSuccess.value.encryptOutput.Some?;
    expect resSuccess.value.encryptOutput.value == KEY_ID_SUCCESS_CASE;
  }

  method TestCallKMSEncrypt_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    // Test with NonExistent
    var input_NonExistent := Kms.Types.EncryptRequest(
      KeyId := KEY_ID_FAILURE_CASE,
      Plaintext := [ 97, 115, 100, 102 ],
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
    );
    var resFailure_NonExistent := client.CallKMSEncrypt(SimpleCallingawssdkfromlocalservice.Types.CallKMSEncryptInput(kmsClient := kmsClient, keyId := KEY_ID_FAILURE_CASE, plaintext := PLAIN_TEXT));

    expect resFailure_NonExistent.Failure?;
    expect resFailure_NonExistent.error.ComAmazonawsKms?;
    expect resFailure_NonExistent.error.ComAmazonawsKms.NotFoundException?;
  }

  method{:test} CallKMSDecrypt(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallKMSDecrypt_Success(client);
    TestCallKMSDecrypt_Failure(client);
  }

  method TestCallKMSDecrypt_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var CiphertextBlob : seq<uint8> := [
      1,   1,   1,   0, 120,  64, 243, 140,  39,  94,  49,   9,
      116,  22, 193,   7,  41,  81,  80,  87,  25, 100, 173, 163,
      239,  28,  33, 233,  76, 139, 160, 189, 188, 157,  15, 180,
      20,   0,   0,   0,  98,  48,  96,   6,   9,  42, 134,  72,
      134, 247,  13,   1,   7,   6, 160,  83,  48,  81,   2,   1,
      0,  48,  76,   6,   9,  42, 134,  72, 134, 247,  13,   1,
      7,   1,  48,  30,   6,   9,  96, 134,  72,   1, 101,   3,
      4,   1,  46,  48,  17,   4,  12, 196, 249,  60,   7,  21,
      231,  87,  70, 216,  12,  31,  13,   2,   1,  16, 128,  31,
      222, 119, 162, 112,  88, 153,  39, 197,  21, 182, 116, 176,
      120, 174, 107,  82, 182, 223, 160, 201,  15,  29,   3, 254,
      3, 208,  72, 171,  64, 207, 175
    ];
    var kmsClient :- expect Kms.KMSClient();
    var resSuccess := client.CallKMSDecrypt(SimpleCallingawssdkfromlocalservice.Types.CallKMSDecryptInput(kmsClient := kmsClient, keyId := KEY_ID_SUCCESS_CASE, ciphertextBlob := workAround(CiphertextBlob)));

    expect resSuccess.Success?;
    expect resSuccess.value.KeyIdType.Some?;
    expect resSuccess.value.Plaintext.Some?;
    expect resSuccess.value.KeyIdType.value == KEY_ID_SUCCESS_CASE;
    expect resSuccess.value.Plaintext.value == [ 165, 191, 67, 62 ];
  }

  method TestCallKMSDecrypt_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var CiphertextBlob : seq<uint8> := [
      1,   1,   1,   0, 120,  64, 243, 140,  39,  94,  49,   9,
      116,  22, 193,   7,  41,  81,  80,  87,  25, 100, 173, 163,
      239,  28,  33, 233,  76, 139, 160, 189, 188, 157,  15, 180,
      20,   0,   0,   0,  98,  48,  96,   6,   9,  42, 134,  72,
      134, 247,  13,   1,   7,   6, 160,  83,  48,  81,   2,   1,
      0,  48,  76,   6,   9,  42, 134,  72, 134, 247,  13,   1,
      7,   1,  48,  30,   6,   9,  96, 134,  72,   1, 101,   3,
      4,   1,  46,  48,  17,   4,  12, 196, 249,  60,   7,  21,
      231,  87,  70, 216,  12,  31,  13,   2,   1,  16, 128,  31,
      222, 119, 162, 112,  88, 153,  39, 197,  21, 182, 116, 176,
      120, 174, 107,  82, 182, 223, 160, 201,  15,  29,   3, 254,
      3, 208,  72, 171,  64, 207, 175
    ];
    var kmsClient :- expect Kms.KMSClient();
    var resFailure := client.CallKMSDecrypt(SimpleCallingawssdkfromlocalservice.Types.CallKMSDecryptInput(kmsClient := kmsClient, keyId := KEY_ID_FAILURE_CASE, ciphertextBlob := workAround(CiphertextBlob)));
    expect resFailure.Failure?;
    expect resFailure.error.ComAmazonawsKms?;
    expect resFailure.error.ComAmazonawsKms.IncorrectKeyException?;
  }

  method{:test} CallKMSGenerateDataKey(){
    var client :- expect SimpleCallingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice();
    TestCallKMSGenerateDataKey_Success(client);
    TestCallKMSGenerateDataKey_Failure(client);
  }

  method TestCallKMSGenerateDataKey_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    var numberOfBytes := 32 as Kms.Types.NumberOfBytesType;
    var resSuccess := client.CallKMSGenerateDataKey(SimpleCallingawssdkfromlocalservice.Types.CallKMSGenerateDataKeyInput(kmsClient := kmsClient, keyId := KEY_ID_SUCCESS_CASE, numberOfBytesType := numberOfBytes));

    expect resSuccess.Success?;
    expect resSuccess.value.ciphertextType.Some?;
    expect resSuccess.value.plaintext.Some?;
    expect resSuccess.value.keyId.Some?;
    expect |resSuccess.value.plaintext.value| == numberOfBytes as nat;
  }

  method TestCallKMSGenerateDataKey_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    var numberOfBytes := 32 as Kms.Types.NumberOfBytesType;
    var resFailure := client.CallKMSGenerateDataKey(SimpleCallingawssdkfromlocalservice.Types.CallKMSGenerateDataKeyInput(kmsClient := kmsClient, keyId := KEY_ID_FAILURE_CASE, numberOfBytesType := numberOfBytes));

    expect resFailure.Failure?;
    expect resFailure.error.ComAmazonawsKms?;
    expect resFailure.error.ComAmazonawsKms.NotFoundException?;
  }
}
