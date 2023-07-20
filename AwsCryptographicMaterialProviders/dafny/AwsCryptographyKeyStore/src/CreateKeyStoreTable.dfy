// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "Structure.dfy"

module CreateKeyStoreTable {
  import opened StandardLibrary
  import opened Wrappers
  import opened Seq
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import Structure

  // KeyStore Definitions
  const ATTRIBUTE_DEFINITIONS: DDB.AttributeDefinitions := [
    DDB.AttributeDefinition(
      AttributeName := Structure.BRANCH_KEY_IDENTIFIER_FIELD,
      AttributeType := DDB.ScalarAttributeType.S),
    DDB.AttributeDefinition(
      AttributeName := Structure.TYPE_FIELD,
      AttributeType := DDB.ScalarAttributeType.S)
  ]
  const KEY_SCHEMA: DDB.KeySchema := [
    DDB.KeySchemaElement(
      AttributeName := Structure.BRANCH_KEY_IDENTIFIER_FIELD,
      KeyType := DDB.KeyType.HASH),
    DDB.KeySchemaElement(
      AttributeName := Structure.TYPE_FIELD,
      KeyType := DDB.KeyType.RANGE)
  ]

  type keyStoreDescription = t: DDB.TableDescription | keyStoreHasExpectedConstruction?(t) witness *
  predicate method keyStoreHasExpectedConstruction?(t: DDB.TableDescription) {
    && t.AttributeDefinitions.Some? && t.KeySchema.Some? && t.TableName.Some? && t.TableArn.Some?
       //= aws-encryption-sdk-specification/framework/branch-key-store.md#keyschema
       //= type=implication
       //# The following KeySchema MUST be configured on the table:
    && ToSet(t.AttributeDefinitions.value) >= ToSet(ATTRIBUTE_DEFINITIONS)
    && ToSet(t.KeySchema.value) >= ToSet(KEY_SCHEMA)
  }

  method CreateKeyStoreTable(tableName: DDB.TableName, ddbClient: DDB.IDynamoDBClient)
    returns (res: Result<string, Types.Error>)
    requires ddbClient.ValidState()
    requires DDB.IsValid_TableName(tableName)
    modifies ddbClient.Modifies
    ensures ddbClient.ValidState()

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
    //= type=implication
    //# This operation MUST first calls the DDB::DescribeTable API with the configured `tableName`.
    ensures
      && |ddbClient.History.DescribeTable| == |old(ddbClient.History.DescribeTable)| + 1
      && Seq.Last(ddbClient.History.DescribeTable).input.TableName == tableName
      && (Seq.Last(ddbClient.History.DescribeTable).output.Success?
          ==> |ddbClient.History.CreateTable| == |old(ddbClient.History.CreateTable)|)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
    //= type=implication
    //# If the client responds with a `ResourceNotFoundException`,
    //# then this operation MUST continue and
    //# MUST call [AWS DDB CreateTable](https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_CreateTable.html)
    //# with the following specifics:
    ensures
      && Seq.Last(ddbClient.History.DescribeTable).output.Failure?
      && Seq.Last(ddbClient.History.DescribeTable).output.error.ResourceNotFoundException?
      ==>
        && |ddbClient.History.CreateTable| == |old(ddbClient.History.CreateTable)| + 1
        && var CreateTableInput := Seq.Last(ddbClient.History.CreateTable).input;
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
        //= type=implication
        //# - TableName is the configured tableName.
        //# - [KeySchema](#keyschema) as defined below.
        && CreateTableInput.TableName == tableName
        && CreateTableInput.KeySchema == KEY_SCHEMA
           //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
           //= type=implication
           //# If the operation fails to create table, the operation MUST fail.
        && (Seq.Last(ddbClient.History.CreateTable).output.Failure? ==> res.Failure?)
           //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
           //= type=implication
           //# If the operation successfully creates a table, the operation MUST return the AWS DDB Table Arn
           //# back to the caller.
        && (
             && Seq.Last(ddbClient.History.CreateTable).output.Success?
             && Seq.Last(ddbClient.History.CreateTable).output.value.TableDescription.Some?
             && keyStoreHasExpectedConstruction?(Seq.Last(ddbClient.History.CreateTable).output.value.TableDescription.value)
             ==>
               && res.Success?
               && res.value == Seq.Last(ddbClient.History.CreateTable).output.value.TableDescription.value.TableArn.value
           )

    ensures
      && Seq.Last(ddbClient.History.DescribeTable).output.Success?
      ==>
        var DescribeTableResult := Seq.Last(ddbClient.History.DescribeTable).output.value;
        if DescribeTableResult.Table.Some? && keyStoreHasExpectedConstruction?(DescribeTableResult.Table.value) then
          // This is approximated by using the given example.
          // The intention is to show that nothing can be proven
          // about such other values.

          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //= type=implication
          //# The table MAY have additional information,
          //# like GlobalSecondaryIndex defined.
          && (DescribeTableResult.Table.value.GlobalSecondaryIndexes.Some? || DescribeTableResult.Table.value.GlobalSecondaryIndexes.None?)
        else
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //= type=implication
          //# If the [KeySchema](#keyschema) does not match
          //# this operation MUST yield an error.
          && res.Failure?
  {
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
    //# This operation MUST first calls the DDB::DescribeTable API with the configured `tableName`.
    var maybeDescribeTableResponse := ddbClient.DescribeTable(
      DDB.DescribeTableInput(
        TableName := tableName
      )
    );

    if maybeDescribeTableResponse.Failure? {
      var error := maybeDescribeTableResponse.error;
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
      //# If the client responds with a `ResourceNotFoundException`,
      //# then this operation MUST continue and
      if error.ResourceNotFoundException? {
        //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
        //# MUST call [AWS DDB CreateTable](https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_CreateTable.html)
        //# with the following specifics:
        var maybeCreateTableResponse := ddbClient.CreateTable(
          DDB.CreateTableInput(
            AttributeDefinitions := ATTRIBUTE_DEFINITIONS,
            TableName := tableName,
            //= aws-encryption-sdk-specification/framework/branch-key-store.md#keyschema
            //# The following KeySchema MUST be configured on the table:
            KeySchema := KEY_SCHEMA,
            LocalSecondaryIndexes := None,
            GlobalSecondaryIndexes := None,
            BillingMode := Some(DDB.BillingMode.PAY_PER_REQUEST) ,
            ProvisionedThroughput :=  None,
            StreamSpecification := None,
            SSESpecification := None,
            Tags := None,
            TableClass := None
          )
        );

        if maybeCreateTableResponse.Failure? {
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //# If the operation fails to create table, the operation MUST fail.
          res := Failure(Types.ComAmazonawsDynamodb(maybeCreateTableResponse.error));
        } else {
          :- Need(
            && maybeCreateTableResponse.value.TableDescription.Some?
            && keyStoreHasExpectedConstruction?(maybeCreateTableResponse.value.TableDescription.value),
            E("Configured table name does not conform to expected Key Store construction.")
          );
          //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
          //# If the operation successfully creates a table, the operation MUST return the AWS DDB Table Arn
          //# back to the caller.
          res := Success(maybeCreateTableResponse.value.TableDescription.value.TableArn.value);
        }
      } else {
        res := Failure(Types.ComAmazonawsDynamodb(error));
      }
    } else {
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkeystore
      //# If the response is successful, this operation validates that the table has the expected
      //# [KeySchema](#keyschema) as defined below.
      //# If the [KeySchema](#keyschema) does not match
      //# this operation MUST yield an error.
      :- Need(
        && maybeDescribeTableResponse.value.Table.Some?
        && keyStoreHasExpectedConstruction?(maybeDescribeTableResponse.value.Table.value),
        E("Configured table name does not conform to expected Key Store construction.")
      );
      res := Success(maybeDescribeTableResponse.value.Table.value.TableArn.value);
    }
  }

  function method E(s : string) : Types.Error {
    Types.KeyStoreException(message := s)
  }
}
