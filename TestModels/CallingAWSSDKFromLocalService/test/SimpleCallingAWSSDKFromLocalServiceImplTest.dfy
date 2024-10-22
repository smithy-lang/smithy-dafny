// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module SimpleCallingAWSSDKFromLocalServiceImplTest {
  import Com.Amazonaws.Dynamodb
  import Com.Amazonaws.Kms
  import SimpleCallingAWSSDKFromLocalService

  // For call to DDB
  const TABLE_ARN_SUCCESS_CASE := "arn:aws:dynamodb:us-west-2:370957321024:table/TestTable"
  const TABLE_ARN_FAILURE_CASE := "arn:aws:dynamodb:us-west-2:370957321024:table/TestTableFailure"
  const NONEXISTENT_TABLE_NAME := "NONEXISTENT_Table"

  // For call to KMS
  const KEY_ID_SUCCESS_CASE := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f"
  const INVALID_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-invalidkeyid"
  const NONEXISTENT_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g"
  // The string "asdf" as bytes
  const PLAIN_TEXT: Kms.Types.PlaintextType := [ 97, 115, 100, 102 ]

  import opened SimpleCallingawssdkfromlocalserviceTypes
  import opened Wrappers
  method{:test} CallDDBScan(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallDDBScan_Success(client);
    TestCallDDBScan_Failure(client);
  }

  method TestCallDDBScan_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
  {
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resSuccess := client.CallDDBScan(SimpleCallingAWSSDKFromLocalService.Types.CallDDBScanInput(ddbClient := ddbClient, tableArn := TABLE_ARN_SUCCESS_CASE));

    expect resSuccess.Success?;
    expect resSuccess.value.itemOutput != -1;
  }

  method TestCallDDBScan_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resFailure := client.CallDDBScan(SimpleCallingAWSSDKFromLocalService.Types.CallDDBScanInput(ddbClient := ddbClient, tableArn := TABLE_ARN_FAILURE_CASE));

    expect resFailure.Failure?;
  }

  method{:test} CallKMSEncrypt(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallKMSEncrypt_Success(client);
    TestCallKMSEncrypt_Failure(client);
  }

  method TestCallKMSEncrypt_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    var resSuccess := client.CallKMSEncrypt(SimpleCallingAWSSDKFromLocalService.Types.CallKMSEncryptInput(kmsClient := kmsClient, keyId := KEY_ID_SUCCESS_CASE, plaintext := PLAIN_TEXT));
    
    expect resSuccess.Success?;
    expect resSuccess.value.encryptOutput == KEY_ID_SUCCESS_CASE;
  }

  method TestCallKMSEncrypt_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect Kms.KMSClient();
    // Test with NonExistent
    var input_NonExistent := Kms.Types.EncryptRequest(
      KeyId := NONEXISTENT_KEY_ID,
      Plaintext := [ 97, 115, 100, 102 ],
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
    );
    var resFailure_NonExistent := client.CallKMSEncrypt(SimpleCallingAWSSDKFromLocalService.Types.CallKMSEncryptInput(kmsClient := kmsClient, keyId := NONEXISTENT_KEY_ID, plaintext := PLAIN_TEXT));
    
    expect resFailure_NonExistent.Failure?;
    expect resFailure_NonExistent.error.ComAmazonawsKms?;
    expect resFailure_NonExistent.error.ComAmazonawsKms.NotFoundException?;
  }
}
