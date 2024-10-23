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

  method{:test} TestCallDDBScan() {
    var client :- expect WrappedSimpleCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallDDBScan_Success(client);
    TestCallDDBScanWrappedCase_Failure(client);
  }

  method{:test} TestCallKMSEncrypt() {
    var client :- expect WrappedSimpleCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMSEncrypt_Success(client);
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMSEncrypt_Failure(client);
  }

  method TestCallDDBScanWrappedCase_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ddbClient :- expect Dynamodb.DynamoDBClient();
    var resFailure := client.CallDDBScan(SimpleCallingAWSSDKFromLocalService.Types.CallDDBScanInput(ddbClient := ddbClient, tableArn := TABLE_ARN_FAILURE_CASE));

    expect resFailure.Failure?;
    // If a table is not found and IAM user have permission on limited DDB table, DDB client returns an opaque error.
    expect resFailure.error.Opaque?;
  }
}
