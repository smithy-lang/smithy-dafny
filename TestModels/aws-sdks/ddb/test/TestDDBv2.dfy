// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestDDBv2 {
    import DDB = Com.Amazonaws.Dynamodb
    import opened StandardLibrary.UInt
    import opened Wrappers
    
    const tableNameTest : DDB.Types.TableName := "TestTable";
    const secIndex : DDB.Types.IndexName := "Active-Keys"

    // We should have basic tests for what the MPL is using DDB for.
    // MPL will interact with DDB through GET, PUT, and Query

    // Queries are used in the Hierarchy Keyring for OnEncrypt
    method {:test} BasicQueryTests() {
        var attributeNameMap := map[
          "#bkid"   := "branch-key-id",
          "#status" := "status"
        ];

        var attributeValueMap: DDB.Types.AttributeMap := map[
          ":bkid"   := DDB.Types.AttributeValue.S("aws-kms-h"),
          ":status" := DDB.Types.AttributeValue.S("ACTIVE")
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
                "#status = :status and #bkid = :bkid"
            ),
            ExpressionAttributeNames := DDB.Wrappers.Some(attributeNameMap),
            ExpressionAttributeValues := DDB.Wrappers.Some(attributeValueMap)
        );
        BasicQueryTest(input := queryInput);
    }

    // MPL uses Get in the Hierarchy Keyring for OnDecrypt
    method {:test} BasicGetTests() {
        var Key2Get: DDB.Types.Key := map[
          "branch-key-id" := DDB.Types.AttributeValue.S("aws-kms-h"),
          "version" := DDB.Types.AttributeValue.S("1")
        ];
        var getInput := DDB.Types.GetItemInput(
            TableName := tableNameTest,
            Key := Key2Get,
            AttributesToGet := DDB.Wrappers.None,
            ConsistentRead := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ProjectionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None
       );
       BasicGetTest(input := getInput);
    }

    // Note that if an item with branch-key-id "aws-kms-put-item" already exists in the table,
    //     running this test will clobber the existing item
    method {:test} BasicPutTests() {
        var attributeValueMap: DDB.Types.AttributeMap := map[
          "branch-key-id"   := DDB.Types.AttributeValue.S("aws-kms-put-item"),
          "status" := DDB.Types.AttributeValue.S("ACTIVE"),
          "version" := DDB.Types.AttributeValue.S("version-1")
        ];

        var putInput := DDB.Types.PutItemInput(
            TableName := tableNameTest,
            Item := attributeValueMap,
            Expected := DDB.Wrappers.None,
            ReturnValues := DDB.Wrappers.None,
            ReturnConsumedCapacity := DDB.Wrappers.None,
            ReturnItemCollectionMetrics := DDB.Wrappers.None,
            ConditionalOperator := DDB.Wrappers.None,
            ConditionExpression := DDB.Wrappers.None,
            ExpressionAttributeNames := DDB.Wrappers.None,
            ExpressionAttributeValues := DDB.Wrappers.None
        );
        BasicPutTest(input := putInput);
    }
    
    method {:test} BatGetItemTests() {
      var attributeNameBranchKey: DDB.Types.AttributeName := "branch-key-id";
      var attributeValueBranchKey: DDB.Types.AttributeValue := DDB.Types.AttributeValue.S(
        "aws-kms-put-item");
      var attributeNameVersion: DDB.Types.AttributeName := "version";
      var attributeValueVersion: DDB.Types.AttributeValue := DDB.Types.AttributeValue.S(
        "version-1");
      var key: DDB.Types.Key := map[
        attributeNameBranchKey := attributeValueBranchKey,
        attributeNameVersion := attributeValueVersion
      ];
      var keys: DDB.Types.KeyList := [ key ];
      var keyAndAttributes := DDB.Types.KeysAndAttributes(
        Keys := keys,
        AttributesToGet := None(),
        ConsistentRead := None(),
        ProjectionExpression := None(),
        ExpressionAttributeNames := None()
      );
      
      var batchGetRequestMap: DDB.Types.BatchGetRequestMap := map[
        tableNameTest := keyAndAttributes
      ];
      
      var batchGetInput := DDB.Types.BatchGetItemInput(
        RequestItems := batchGetRequestMap,
        ReturnConsumedCapacity := DDB.Wrappers.None()
      );
      BatchGetItemTest(input := batchGetInput);
    }

    method BasicQueryTest(
        nameonly input: DDB.Types.QueryInput
    )
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.Query(input);

        // print ret;

        expect(ret.Success?);

        var queryOutput := ret.value;

        expect queryOutput.Items.Some?;

        var queryItem := queryOutput.Items.value;
        expect |queryItem| > 0;

        var item := queryItem[0];

        // we only expect these keys
        expect item.Keys == {"branch-key-id", "version", "create-time", "enc", "hierarchy-version", "status"};
        // we expect that for every key there is a value
        expect |item.Keys| == |item.Values|;

    }

    method BasicGetTest(
        nameonly input: DDB.Types.GetItemInput
    )
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.GetItem(input);

        // print ret;

        expect(ret.Success?);

        var itemOutput := ret.value;
        expect itemOutput.Item.Some?;

        var item := itemOutput.Item.value;
        expect item.Keys == {"branch-key-id", "version", "create-time", "enc", "hierarchy-version", "status"};
        expect |item.Keys| == |item.Values|;
    }

    method BasicPutTest(
        nameonly input: DDB.Types.PutItemInput
    )
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.PutItem(input);

        // print ret;

        expect(ret.Success?);
    }

    method BatchGetItemTest(
        nameonly input: DDB.Types.BatchGetItemInput
    )
    {
        var client :- expect DDB.DynamoDBClient();

        var ret := client.BatchGetItem(input);

        if (ret.Failure?) {
          print("\n\t BatchGetItemTest Failed");
          print("\n\t");
          print(ret);
          print("\n");
        }

        expect(ret.Success?);
    }

    
}
