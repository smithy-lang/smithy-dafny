// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"

module SimpleCallingAWSSDKFromLocalServiceImplTest {
  import ComAmazonawsDynamodbTypes
  import SimpleCallingAWSSDKFromLocalService

  import opened SimpleCallingawssdkfromlocalserviceTypes
  import opened Wrappers
  method{:test} BasicGet(){
    var client :- expect SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalService();
    TestBasicGet(client);
  }

  method TestBasicGet(client: ISimpleCallingAWSSDKFromLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var Key2Get: ComAmazonawsDynamodbTypes.Key := map[
          "branch-key-id" := ComAmazonawsDynamodbTypes.AttributeValue.S("aws-kms-h"),
          "version" := ComAmazonawsDynamodbTypes.AttributeValue.S("1")
        ];
    var getInput := ComAmazonawsDynamodbTypes.GetItemInput(
      TableName := "tableNameTest",
      Key := Key2Get,
      AttributesToGet := ComAmazonawsDynamodbTypes.Wrappers.None,
        ConsistentRead := ComAmazonawsDynamodbTypes.Wrappers.None,
            ReturnConsumedCapacity := ComAmazonawsDynamodbTypes.Wrappers.None,
            ProjectionExpression := ComAmazonawsDynamodbTypes.Wrappers.None,
            ExpressionAttributeNames := ComAmazonawsDynamodbTypes.Wrappers.None
    );
    var ret := client.BasicGet(SimpleCallingAWSSDKFromLocalService.Types.BasicGetInput(item := getInput));
    print ret;
  }
}