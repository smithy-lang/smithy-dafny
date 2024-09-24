// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"
include "SimpleCallingAWSSDKFromLocalServiceImplTest.dfy"

module WrappedSimpleCallingAWSSDKFromLocalServiceTest {
  import Com.Amazonaws.Kms
  import SimpleCallingAWSSDKFromLocalService

  import opened WrappedSimpleCallingAWSSDKFromLocalServiceService
  import SimpleCallingAWSSDKFromLocalServiceImplTest
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened SimpleCallingawssdkfromlocalserviceTypes

  const NONEXISTENT_KEY_ID := "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g"
  // The string "asdf" as bytes
  const PLAIN_TEXT: Kms.Types.PlaintextType := [ 97, 115, 100, 102 ]

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
}