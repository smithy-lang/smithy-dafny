// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"
include "SimpleCallingAWSSDKFromLocalServiceImplTest.dfy"

module WrappedSimpleCallingAWSSDKFromLocalServiceTest {
  import Com.Amazonaws.Kms
  import Com.Amazonaws.Dynamodb
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
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallDDBScan_Failure(client);
  }

  method{:test} TestCallKMSEncrypt() {
    var client :- expect WrappedSimpleCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMSEncrypt_Success(client);
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMSEncrypt_Failure(client);
  }
}
