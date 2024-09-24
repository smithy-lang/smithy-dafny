// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"
include "SimpleCallingAWSSDKFromLocalServiceImplTest.dfy"

module WrappedSimpleCallingAWSSDKFromLocalServiceTest {
  import Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import SimpleCallingAWSSDKFromLocalService

  import opened WrappedSimpleCallingAWSSDKFromLocalServiceService
  import SimpleCallingAWSSDKFromLocalServiceImplTest
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened SimpleCallingawssdkfromlocalserviceTypes

  const TABLE_ARN_FAILURE_CASE := "arn:aws:dynamodb:us-west-2:370957321024:table/TestTableFailure"
  const NONEXISTENT_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g"
  // The string "asdf" as bytes
  const PLAIN_TEXT: Kms.Types.PlaintextType := [ 97, 115, 100, 102 ]

  method{:test} TestCallDDBScan() {
    var client :- expect WrappedSimpleCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallDDBScan_Success(client);
    TestCallDDBScan_Failure(client);
  }

  method{:test} TestCallKMSEncrypt() {
    var client :- expect WrappedSimpleCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMSEncrypt_Success(client);
    TestCallKMSEncrypt_Failure(client);
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
    expect resFailure_NonExistent.error.ComAmazonawsKms.NotFoundException?;
  }

  method TestCallDDBScan_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var resFailure := client.CallDDBGetItem(SimpleCallingAWSSDKFromLocalService.Types.CallDDBGetItemInput(ddbClient := ddbClient, tableArn := TABLE_ARN_FAILURE_CASE));
    print(resFailure);
    expect resFailure.Failure?;
  }
}