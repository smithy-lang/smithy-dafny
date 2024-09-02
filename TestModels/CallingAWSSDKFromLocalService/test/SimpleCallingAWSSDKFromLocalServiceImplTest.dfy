// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module SimpleCallingAWSSDKFromLocalServiceImplTest {
  import DDB = Com.Amazonaws.Dynamodb
  import KMS = Com.Amazonaws.Kms
  import SimpleCallingAWSSDKFromLocalService

  // For call to DDB
  const TABLE_NAME_SUCCESS_CASE := "TestTable"
  const NONEXISTENT_TABLE_NAME := "NONEXISTENT_Table"
  
  // For call to KMS 
  const KEY_ID_SUCCESS_CASE := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
  const INVALID_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-invalidkeyid"
  const NONEXISTENT_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g"
  // The string "asdf" as bytes
  const PLAIN_TEXT := [ 97, 115, 100, 102 ]

  import opened SimpleCallingawssdkfromlocalserviceTypes
  import opened Wrappers
  method{:test} CallDDBGetItem(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallDDBGetItem_Success(client);
    TestCallDDBGetItem_Failure(client);
  }

  method TestCallDDBGetItem_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var Key2Get: DDB.Types.Key := map[
          "branch-key-id" := DDB.Types.AttributeValue.S("aws-kms-h"),
          "version" := DDB.Types.AttributeValue.S("1")
        ];

    var input := DDB.Types.GetItemInput(
            TableName := TABLE_NAME_SUCCESS_CASE,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
    );

    var resSuccess := client.CallDDBGetItem(SimpleCallingAWSSDKFromLocalService.Types.CallDDBGetItemInput(ddbClient := ddbClient, itemInput := input));
    expect resSuccess.Success?;
  }

  method TestCallDDBGetItem_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var Key2Get: DDB.Types.Key := map[
          "branch-key-id" := DDB.Types.AttributeValue.S("aws-kms-h"),
          "version" := DDB.Types.AttributeValue.S("1")
        ];
    var input := DDB.Types.GetItemInput(
            TableName := NONEXISTENT_TABLE_NAME,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
    );
    var resFailure := client.CallDDBGetItem(SimpleCallingAWSSDKFromLocalService.Types.CallDDBGetItemInput(ddbClient := ddbClient, itemInput := input));

    expect resFailure.Failure?;
    print(resFailure);
    print(resFailure.error.Opaque?);
    print(resFailure.error.ComAmazonawsDynamodb?);
  }

  method{:test} CallKMSEncrypt(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallKMSEncrypt_Success(client);
  }

  method TestCallKMSEncrypt_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
  {
    var kmsClient :- expect KMS.KMSClient();
    var input := KMS.Types.EncryptRequest(
      KeyId := KEY_ID_SUCCESS_CASE,
      Plaintext := [ 97, 115, 100, 102 ],
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
      );
    var resSuccess := client.CallKMSEncrypt(SimpleCallingAWSSDKFromLocalService.Types.CallKMSEncryptInput(kmsClient := kmsClient, encryptInput := input));
    expect resSuccess.Success?;
  }

  method TestCallKMSEncrypt_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect KMS.KMSClient();

    // Test with InvalidKey
    var input_InvalidKey := KMS.Types.EncryptRequest(
      KeyId := INVALID_KEY_ID,
      Plaintext := [ 97, 115, 100, 102 ],
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
      );
    var resFailure_InvalidKey := client.CallKMSEncrypt(SimpleCallingAWSSDKFromLocalService.Types.CallKMSEncryptInput(kmsClient := kmsClient, encryptInput := input_InvalidKey));
    expect resFailure_InvalidKey.Failure?;

    // Test with NonExistent
    var input_NonExistent := KMS.Types.EncryptRequest(
      KeyId := NONEXISTENT_KEY_ID,
      Plaintext := [ 97, 115, 100, 102 ],
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
      );
    var resFailure_NonExistent := client.CallKMSEncrypt(SimpleCallingAWSSDKFromLocalService.Types.CallKMSEncryptInput(kmsClient := kmsClient, encryptInput := input_NonExistent));
    expect resFailure_NonExistent.Failure?;
  }
}