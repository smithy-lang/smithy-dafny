// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestComAmazonawsDynamoDB {
    import DDB = Com.Amazonaws.Dynamodb
    import opened StandardLibrary.UInt
    import opened Wrappers

    // Use the infra we have already set up for KeyStore testing
    // to test DynamoDb. Currently relies on some KeyStore specific logic to test.
    const tableNameTest : DDB.Types.TableName := "KeyStoreTestTable";
    const secIndex : DDB.Types.IndexName := "Active-Keys"

    // Basic smoke test for DDB client.
    // Perform in single test to ensure item exists for Get/Query
    method {:test} BasicPutGetQuery() {

        var client :- expect DDB.DynamoDBClient();

        // Test PutItem

        var item: DDB.Types.AttributeMap := map[
          "branch-key-id" := DDB.Types.AttributeValue.S("ddb-client-test"),
          "type" := DDB.Types.AttributeValue.S("ddb-client-test"),
          "status" := DDB.Types.AttributeValue.S("ACTIVE")
        ];

        var putInput := DDB.Types.PutItemInput(
            Item := item,
            TableName := tableNameTest,
            Expected := None,
            ReturnValues := None,
            ReturnConsumedCapacity := None,
            ReturnItemCollectionMetrics := None,
            ConditionalOperator := None,
            ConditionExpression := None,
            ExpressionAttributeNames := None,
            ExpressionAttributeValues := None
        );

        var putRet := client.PutItem(putInput);
        expect putRet.Success?;

        // Test GetItem

        var Key2Get: DDB.Types.Key := map[
          "branch-key-id" := DDB.Types.AttributeValue.S("ddb-client-test"),
          "type" := DDB.Types.AttributeValue.S("ddb-client-test")
        ];
        var getInput := DDB.Types.GetItemInput(
            TableName := tableNameTest,
            Key := Key2Get,
            AttributesToGet := None,
            ConsistentRead := None,
            ReturnConsumedCapacity := None,
            ProjectionExpression := None,
            ExpressionAttributeNames := None
       );

        var getRet := client.GetItem(getInput);
        expect getRet.Success?;

        var itemOutput := getRet.value;
        expect itemOutput.Item.Some?;
        var gotItem := itemOutput.Item.value;
        expect gotItem == item;

        // Test Query

        var attributeNameMap := map[
          "#status" := "status",
          "#branchKeyId" := "branch-key-id"
        ];
        var attributeValueMap: DDB.Types.AttributeMap := map[
          ":status" := DDB.Types.AttributeValue.S("ACTIVE"),
          ":branchKeyId" := DDB.Types.AttributeValue.S("ddb-client-test")
        ];
        var queryInput := DDB.Types.QueryInput(
            TableName := tableNameTest,
            IndexName := DDB.Wrappers.Some(secIndex),
            Select := DDB.Wrappers.None,
            AttributesToGet := DDB.Wrappers.None,
            Limit := DDB.Wrappers.None,
            ConsistentRead :=  DDB.Wrappers.None,
            KeyConditions := DDB.Wrappers.None,
            QueryFilter := DDB.Wrappers.None,
            ConditionalOperator := DDB.Wrappers.None,
            ScanIndexForward := DDB.Wrappers.None,
            ExclusiveStartKey := DDB.Wrappers.None,
            ReturnConsumedCapacity :=  DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            FilterExpression := DDB.Wrappers.None,
            KeyConditionExpression := DDB.Wrappers.Some(
                "#status = :status and #branchKeyId = :branchKeyId"
            ),
            ExpressionAttributeNames := DDB.Wrappers.Some(attributeNameMap),
            ExpressionAttributeValues := DDB.Wrappers.Some(attributeValueMap)
        );

        var queryRet := client.Query(queryInput);
        expect queryRet.Success?;

        var queryOutput := queryRet.value;
        expect queryOutput.Items.Some?;
        var queryItem := queryOutput.Items.value;
        expect |queryItem| == 1;
        var queriedItem := queryItem[0];
        expect item == queriedItem;
    }
}
