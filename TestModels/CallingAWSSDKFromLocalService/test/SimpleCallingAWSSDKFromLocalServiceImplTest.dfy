// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module SimpleCallingAWSSDKFromLocalServiceImplTest {
  import DDB = Com.Amazonaws.Dynamodb
  import KMS = Com.Amazonaws.Kms
  import SimpleCallingAWSSDKFromLocalService

  import opened SimpleCallingawssdkfromlocalserviceTypes
  import opened Wrappers
  method{:test} CallDDB(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallDDB_Success(client);
    TestCallDDB_Failure(client);
  }

  // method TestCallDDB(client: ISimpleCallingAWSSDKFromLocalServiceClient)
  //   requires client.ValidState()
  //   modifies client.Modifies
  //   ensures client.ValidState()
  // {
  //   var resSuccess := TestCallDDB_Success(client);
  //   expect resSuccess.Success?;

  //   var resFailure := TestCallDDB_Failure(client);
  //   expect resFailure.Failure?;
  //   print(resFailure.error);
  //   expect resFailure.error.ComAmazonawsDynamodb?;
  //   expect resFailure.error.ComAmazonawsDynamodb.message.Some?;
  //   expect resFailure.error.ComAmazonawsDynamodb.message.UnwrapOr("") == "Requested resource not found";
  // }

  method TestCallDDB_Success(client: ISimpleCallingAWSSDKFromLocalServiceClient)
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var tableName : DDB.Types.TableName := "BasicPutGetExample";
    var Key2Get: DDB.Types.Key := map[
          "partition_key" := DDB.Types.AttributeValue.S("BasicPutGetExample"),
          "sort_key" := DDB.Types.AttributeValue.N("0")
        ];

    var input := DDB.Types.GetItemInput(
            TableName := tableName,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
    );

    var resSuccess := client.CallDDB(SimpleCallingAWSSDKFromLocalService.Types.CallDDBInput(ddbClient := ddbClient, itemInput := input));
    expect resSuccess.Success?;
  }

  method TestCallDDB_Failure(client: ISimpleCallingAWSSDKFromLocalServiceClient)
  {
    var ddbClient :- expect DDB.DynamoDBClient();
    var tableName : DDB.Types.TableName := "FailureCase";
    var Key2Get: DDB.Types.Key := map[
          "partition_key" := DDB.Types.AttributeValue.S("BasicPutGetExampleYo"),
          "sort_key" := DDB.Types.AttributeValue.N("0")
        ];
    var input := DDB.Types.GetItemInput(
            TableName := tableName,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
    );
    var resFailure := client.CallDDB(SimpleCallingAWSSDKFromLocalService.Types.CallDDBInput(ddbClient := ddbClient, itemInput := input));

    expect resFailure.Failure?;
    print(resFailure.error);
    expect resFailure.error.message == "Requested resource not found";
  }

  method{:test} CallKMS(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestCallKMS(client);
  }

  method TestCallKMS(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ret := client.CallKMS(SimpleCallingAWSSDKFromLocalService.Types.CallKMSInput(kmsClient := kmsClient));
    expect ret.Success?;
  }
}