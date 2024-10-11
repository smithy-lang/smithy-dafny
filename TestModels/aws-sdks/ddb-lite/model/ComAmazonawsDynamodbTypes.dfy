// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../dafny-dependencies/StandardLibrary/src/Index.dfy"
module {:extern "software.amazon.cryptography.services.dynamodb.internaldafny.types" } ComAmazonawsDynamodbTypes
{
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
    // Generic helpers for verification of mock/unit tests.
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  // Begin Generated Types

  type ArchivalReason = string
  datatype ArchivalSummary = | ArchivalSummary (
    nameonly ArchivalDateTime: Option<string> := Option.None ,
    nameonly ArchivalReason: Option<ArchivalReason> := Option.None ,
    nameonly ArchivalBackupArn: Option<BackupArn> := Option.None
  )
  datatype AttributeAction =
    | ADD
    | PUT
    | DELETE
  datatype AttributeDefinition = | AttributeDefinition (
    nameonly AttributeName: KeySchemaAttributeName ,
    nameonly AttributeType: ScalarAttributeType
  )
  type AttributeDefinitions = seq<AttributeDefinition>
  type AttributeMap = map<AttributeName, AttributeValue>
  type AttributeName = x: string | IsValid_AttributeName(x) witness *
  predicate method IsValid_AttributeName(x: string) {
    ( 0 <= |x| <= 65535 )
  }
  type AttributeNameList = x: seq<AttributeName> | IsValid_AttributeNameList(x) witness *
  predicate method IsValid_AttributeNameList(x: seq<AttributeName>) {
    ( 1 <= |x|  )
  }
  type AttributeUpdates = map<AttributeName, AttributeValueUpdate>
  datatype AttributeValue =
    | S(S: StringAttributeValue)
    | N(N: NumberAttributeValue)
    | B(B: BinaryAttributeValue)
    | SS(SS: StringSetAttributeValue)
    | NS(NS: NumberSetAttributeValue)
    | BS(BS: BinarySetAttributeValue)
    | M(M: MapAttributeValue)
    | L(L: ListAttributeValue)
    | NULL(NULL: NullAttributeValue)
    | BOOL(BOOL: BooleanAttributeValue)
  type AttributeValueList = seq<AttributeValue>
  datatype AttributeValueUpdate = | AttributeValueUpdate (
    nameonly Value: Option<AttributeValue> := Option.None ,
    nameonly Action: Option<AttributeAction> := Option.None
  )
  type Backfilling = bool
  type BackupArn = x: string | IsValid_BackupArn(x) witness *
  predicate method IsValid_BackupArn(x: string) {
    ( 37 <= |x| <= 1024 )
  }
  datatype BatchExecuteStatementInput = | BatchExecuteStatementInput (
    nameonly Statements: PartiQLBatchRequest ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None
  )
  datatype BatchExecuteStatementOutput = | BatchExecuteStatementOutput (
    nameonly Responses: Option<PartiQLBatchResponse> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None
  )
  datatype BatchGetItemInput = | BatchGetItemInput (
    nameonly RequestItems: BatchGetRequestMap ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None
  )
  datatype BatchGetItemOutput = | BatchGetItemOutput (
    nameonly Responses: Option<BatchGetResponseMap> := Option.None ,
    nameonly UnprocessedKeys: Option<BatchGetRequestMap> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None
  )
  type BatchGetRequestMap = x: map<TableName, KeysAndAttributes> | IsValid_BatchGetRequestMap(x) witness *
  predicate method IsValid_BatchGetRequestMap(x: map<TableName, KeysAndAttributes>) {
    ( 1 <= |x| <= 100 )
  }
  type BatchGetResponseMap = map<TableName, ItemList>
  datatype BatchStatementError = | BatchStatementError (
    nameonly Code: Option<BatchStatementErrorCodeEnum> := Option.None ,
    nameonly Message: Option<String> := Option.None
  )
  datatype BatchStatementErrorCodeEnum =
    | ConditionalCheckFailed
    | ItemCollectionSizeLimitExceeded
    | RequestLimitExceeded
    | ValidationError
    | ProvisionedThroughputExceeded
    | TransactionConflict
    | ThrottlingError
    | InternalServerError
    | ResourceNotFound
    | AccessDenied
    | DuplicateItem
  datatype BatchStatementRequest = | BatchStatementRequest (
    nameonly Statement: PartiQLStatement ,
    nameonly Parameters: Option<PreparedStatementParameters> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None
  )
  datatype BatchStatementResponse = | BatchStatementResponse (
    nameonly Error: Option<BatchStatementError> := Option.None ,
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly Item: Option<AttributeMap> := Option.None
  )
  datatype BatchWriteItemInput = | BatchWriteItemInput (
    nameonly RequestItems: BatchWriteItemRequestMap ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> := Option.None
  )
  datatype BatchWriteItemOutput = | BatchWriteItemOutput (
    nameonly UnprocessedItems: Option<BatchWriteItemRequestMap> := Option.None ,
    nameonly ItemCollectionMetrics: Option<ItemCollectionMetricsPerTable> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None
  )
  type BatchWriteItemRequestMap = x: map<TableName, WriteRequests> | IsValid_BatchWriteItemRequestMap(x) witness *
  predicate method IsValid_BatchWriteItemRequestMap(x: map<TableName, WriteRequests>) {
    ( 1 <= |x| <= 25 )
  }
  datatype BillingMode =
    | PROVISIONED
    | PAY_PER_REQUEST
  datatype BillingModeSummary = | BillingModeSummary (
    nameonly BillingMode: Option<BillingMode> := Option.None ,
    nameonly LastUpdateToPayPerRequestDateTime: Option<string> := Option.None
  )
  type BinaryAttributeValue = seq<uint8>
  type BinarySetAttributeValue = seq<BinaryAttributeValue>
  type BooleanAttributeValue = bool
  type BooleanObject = bool
  datatype CancellationReason = | CancellationReason (
    nameonly Item: Option<AttributeMap> := Option.None ,
    nameonly Code: Option<Code> := Option.None ,
    nameonly Message: Option<ErrorMessage> := Option.None
  )
  type CancellationReasonList = x: seq<CancellationReason> | IsValid_CancellationReasonList(x) witness *
  predicate method IsValid_CancellationReasonList(x: seq<CancellationReason>) {
    ( 1 <= |x| <= 25 )
  }
  datatype Capacity = | Capacity (
    nameonly ReadCapacityUnits: Option<ConsumedCapacityUnits> := Option.None ,
    nameonly WriteCapacityUnits: Option<ConsumedCapacityUnits> := Option.None ,
    nameonly CapacityUnits: Option<ConsumedCapacityUnits> := Option.None
  )
  type ClientRequestToken = x: string | IsValid_ClientRequestToken(x) witness *
  predicate method IsValid_ClientRequestToken(x: string) {
    ( 1 <= |x| <= 36 )
  }
  type Code = string
  datatype ComparisonOperator =
    | EQ
    | NE
    | IN
    | LE
    | LT
    | GE
    | GT
    | BETWEEN
    | NOT_NULL
    | NULL
    | CONTAINS
    | NOT_CONTAINS
    | BEGINS_WITH
  datatype Condition = | Condition (
    nameonly AttributeValueList: Option<AttributeValueList> := Option.None ,
    nameonly ComparisonOperator: ComparisonOperator
  )
  datatype ConditionalOperator =
    | AND
    | OR
  datatype ConditionCheck = | ConditionCheck (
    nameonly Key: Key ,
    nameonly TableName: TableName ,
    nameonly ConditionExpression: ConditionExpression ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure> := Option.None
  )
  type ConditionExpression = string
  type ConsistentRead = bool
  datatype ConsumedCapacity = | ConsumedCapacity (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly CapacityUnits: Option<ConsumedCapacityUnits> := Option.None ,
    nameonly ReadCapacityUnits: Option<ConsumedCapacityUnits> := Option.None ,
    nameonly WriteCapacityUnits: Option<ConsumedCapacityUnits> := Option.None ,
    nameonly Table: Option<Capacity> := Option.None ,
    nameonly LocalSecondaryIndexes: Option<SecondaryIndexesCapacityMap> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<SecondaryIndexesCapacityMap> := Option.None
  )
  type ConsumedCapacityMultiple = seq<ConsumedCapacity>
  type ConsumedCapacityUnits = x: seq<uint8> | IsValid_ConsumedCapacityUnits(x) witness *
  predicate method IsValid_ConsumedCapacityUnits(x: seq<uint8>) {
    ( 8 <= |x| <= 8 )
  }
  datatype CreateTableInput = | CreateTableInput (
    nameonly AttributeDefinitions: AttributeDefinitions ,
    nameonly TableName: TableName ,
    nameonly KeySchema: KeySchema ,
    nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexList> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexList> := Option.None ,
    nameonly BillingMode: Option<BillingMode> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None ,
    nameonly StreamSpecification: Option<StreamSpecification> := Option.None ,
    nameonly SSESpecification: Option<SSESpecification> := Option.None ,
    nameonly Tags: Option<TagList> := Option.None ,
    nameonly TableClass: Option<TableClass> := Option.None
  )
  datatype CreateTableOutput = | CreateTableOutput (
    nameonly TableDescription: Option<TableDescription> := Option.None
  )
  datatype Delete = | Delete (
    nameonly Key: Key ,
    nameonly TableName: TableName ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure> := Option.None
  )
  datatype DeleteItemInput = | DeleteItemInput (
    nameonly TableName: TableName ,
    nameonly Key: Key ,
    nameonly Expected: Option<ExpectedAttributeMap> := Option.None ,
    nameonly ConditionalOperator: Option<ConditionalOperator> := Option.None ,
    nameonly ReturnValues: Option<ReturnValue> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> := Option.None ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None
  )
  datatype DeleteItemOutput = | DeleteItemOutput (
    nameonly Attributes: Option<AttributeMap> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None ,
    nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics> := Option.None
  )
  datatype DeleteRequest = | DeleteRequest (
    nameonly Key: Key
  )
  datatype DescribeTableInput = | DescribeTableInput (
    nameonly TableName: TableName
  )
  datatype DescribeTableOutput = | DescribeTableOutput (
    nameonly Table: Option<TableDescription> := Option.None
  )
  class IDynamoDBClientCallHistory {
    ghost constructor() {
      BatchExecuteStatement := [];
      BatchGetItem := [];
      BatchWriteItem := [];
      CreateTable := [];
      DeleteItem := [];
      DescribeTable := [];
      ExecuteStatement := [];
      ExecuteTransaction := [];
      GetItem := [];
      PutItem := [];
      Query := [];
      Scan := [];
      TransactGetItems := [];
      TransactWriteItems := [];
      UpdateItem := [];
    }
    ghost var BatchExecuteStatement: seq<DafnyCallEvent<BatchExecuteStatementInput, Result<BatchExecuteStatementOutput, Error>>>
    ghost var BatchGetItem: seq<DafnyCallEvent<BatchGetItemInput, Result<BatchGetItemOutput, Error>>>
    ghost var BatchWriteItem: seq<DafnyCallEvent<BatchWriteItemInput, Result<BatchWriteItemOutput, Error>>>
    ghost var CreateTable: seq<DafnyCallEvent<CreateTableInput, Result<CreateTableOutput, Error>>>
    ghost var DeleteItem: seq<DafnyCallEvent<DeleteItemInput, Result<DeleteItemOutput, Error>>>
    ghost var DescribeTable: seq<DafnyCallEvent<DescribeTableInput, Result<DescribeTableOutput, Error>>>
    ghost var ExecuteStatement: seq<DafnyCallEvent<ExecuteStatementInput, Result<ExecuteStatementOutput, Error>>>
    ghost var ExecuteTransaction: seq<DafnyCallEvent<ExecuteTransactionInput, Result<ExecuteTransactionOutput, Error>>>
    ghost var GetItem: seq<DafnyCallEvent<GetItemInput, Result<GetItemOutput, Error>>>
    ghost var PutItem: seq<DafnyCallEvent<PutItemInput, Result<PutItemOutput, Error>>>
    ghost var Query: seq<DafnyCallEvent<QueryInput, Result<QueryOutput, Error>>>
    ghost var Scan: seq<DafnyCallEvent<ScanInput, Result<ScanOutput, Error>>>
    ghost var TransactGetItems: seq<DafnyCallEvent<TransactGetItemsInput, Result<TransactGetItemsOutput, Error>>>
    ghost var TransactWriteItems: seq<DafnyCallEvent<TransactWriteItemsInput, Result<TransactWriteItemsOutput, Error>>>
    ghost var UpdateItem: seq<DafnyCallEvent<UpdateItemInput, Result<UpdateItemOutput, Error>>>
  }
  trait {:termination false} IDynamoDBClient
  {
    // Helper to define any additional modifies/reads clauses.
    // If your operations need to mutate state,
    // add it in your constructor function:
    // Modifies := {your, fields, here, History};
    // If you do not need to mutate anything:
    // Modifies := {History};

    ghost const Modifies: set<object>
    // For an unassigned field defined in a trait,
    // Dafny can only assign a value in the constructor.
    // This means that for Dafny to reason about this value,
    // it needs some way to know (an invariant),
    // about the state of the object.
    // This builds on the Valid/Repr paradigm
    // To make this kind requires safe to add
    // to methods called from unverified code,
    // the predicate MUST NOT take any arguments.
    // This means that the correctness of this requires
    // MUST only be evaluated by the class itself.
    // If you require any additional mutation,
    // then you MUST ensure everything you need in ValidState.
    // You MUST also ensure ValidState in your constructor.
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    ghost const History: IDynamoDBClientCallHistory
    predicate BatchExecuteStatementEnsuresPublicly(input: BatchExecuteStatementInput , output: Result<BatchExecuteStatementOutput, Error>)
    // The public method to be called by library consumers
    method BatchExecuteStatement ( input: BatchExecuteStatementInput )
      returns (output: Result<BatchExecuteStatementOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`BatchExecuteStatement
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures BatchExecuteStatementEnsuresPublicly(input, output)
      ensures History.BatchExecuteStatement == old(History.BatchExecuteStatement) + [DafnyCallEvent(input, output)]

    predicate BatchGetItemEnsuresPublicly(input: BatchGetItemInput , output: Result<BatchGetItemOutput, Error>)
    // The public method to be called by library consumers
    method BatchGetItem ( input: BatchGetItemInput )
      returns (output: Result<BatchGetItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`BatchGetItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures BatchGetItemEnsuresPublicly(input, output)
      ensures History.BatchGetItem == old(History.BatchGetItem) + [DafnyCallEvent(input, output)]

    predicate BatchWriteItemEnsuresPublicly(input: BatchWriteItemInput , output: Result<BatchWriteItemOutput, Error>)
    // The public method to be called by library consumers
    method BatchWriteItem ( input: BatchWriteItemInput )
      returns (output: Result<BatchWriteItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`BatchWriteItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures BatchWriteItemEnsuresPublicly(input, output)
      ensures History.BatchWriteItem == old(History.BatchWriteItem) + [DafnyCallEvent(input, output)]

    predicate CreateTableEnsuresPublicly(input: CreateTableInput , output: Result<CreateTableOutput, Error>)
    // The public method to be called by library consumers
    method CreateTable ( input: CreateTableInput )
      returns (output: Result<CreateTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateTableEnsuresPublicly(input, output)
      ensures History.CreateTable == old(History.CreateTable) + [DafnyCallEvent(input, output)]

    predicate DeleteItemEnsuresPublicly(input: DeleteItemInput , output: Result<DeleteItemOutput, Error>)
    // The public method to be called by library consumers
    method DeleteItem ( input: DeleteItemInput )
      returns (output: Result<DeleteItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteItemEnsuresPublicly(input, output)
      ensures History.DeleteItem == old(History.DeleteItem) + [DafnyCallEvent(input, output)]

    predicate DescribeTableEnsuresPublicly(input: DescribeTableInput , output: Result<DescribeTableOutput, Error>)
    // The public method to be called by library consumers
    method DescribeTable ( input: DescribeTableInput )
      returns (output: Result<DescribeTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeTableEnsuresPublicly(input, output)
      ensures History.DescribeTable == old(History.DescribeTable) + [DafnyCallEvent(input, output)]

    predicate ExecuteStatementEnsuresPublicly(input: ExecuteStatementInput , output: Result<ExecuteStatementOutput, Error>)
    // The public method to be called by library consumers
    method ExecuteStatement ( input: ExecuteStatementInput )
      returns (output: Result<ExecuteStatementOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ExecuteStatement
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ExecuteStatementEnsuresPublicly(input, output)
      ensures History.ExecuteStatement == old(History.ExecuteStatement) + [DafnyCallEvent(input, output)]

    predicate ExecuteTransactionEnsuresPublicly(input: ExecuteTransactionInput , output: Result<ExecuteTransactionOutput, Error>)
    // The public method to be called by library consumers
    method ExecuteTransaction ( input: ExecuteTransactionInput )
      returns (output: Result<ExecuteTransactionOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ExecuteTransaction
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ExecuteTransactionEnsuresPublicly(input, output)
      ensures History.ExecuteTransaction == old(History.ExecuteTransaction) + [DafnyCallEvent(input, output)]

    predicate GetItemEnsuresPublicly(input: GetItemInput , output: Result<GetItemOutput, Error>)
    // The public method to be called by library consumers
    method GetItem ( input: GetItemInput )
      returns (output: Result<GetItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetItemEnsuresPublicly(input, output)
      ensures History.GetItem == old(History.GetItem) + [DafnyCallEvent(input, output)]

    predicate PutItemEnsuresPublicly(input: PutItemInput , output: Result<PutItemOutput, Error>)
    // The public method to be called by library consumers
    method PutItem ( input: PutItemInput )
      returns (output: Result<PutItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`PutItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures PutItemEnsuresPublicly(input, output)
      ensures History.PutItem == old(History.PutItem) + [DafnyCallEvent(input, output)]

    predicate QueryEnsuresPublicly(input: QueryInput , output: Result<QueryOutput, Error>)
    // The public method to be called by library consumers
    method Query ( input: QueryInput )
      returns (output: Result<QueryOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Query
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures QueryEnsuresPublicly(input, output)
      ensures History.Query == old(History.Query) + [DafnyCallEvent(input, output)]

    predicate ScanEnsuresPublicly(input: ScanInput , output: Result<ScanOutput, Error>)
    // The public method to be called by library consumers
    method Scan ( input: ScanInput )
      returns (output: Result<ScanOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Scan
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ScanEnsuresPublicly(input, output)
      ensures History.Scan == old(History.Scan) + [DafnyCallEvent(input, output)]

    predicate TransactGetItemsEnsuresPublicly(input: TransactGetItemsInput , output: Result<TransactGetItemsOutput, Error>)
    // The public method to be called by library consumers
    method TransactGetItems ( input: TransactGetItemsInput )
      returns (output: Result<TransactGetItemsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`TransactGetItems
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures TransactGetItemsEnsuresPublicly(input, output)
      ensures History.TransactGetItems == old(History.TransactGetItems) + [DafnyCallEvent(input, output)]

    predicate TransactWriteItemsEnsuresPublicly(input: TransactWriteItemsInput , output: Result<TransactWriteItemsOutput, Error>)
    // The public method to be called by library consumers
    method TransactWriteItems ( input: TransactWriteItemsInput )
      returns (output: Result<TransactWriteItemsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`TransactWriteItems
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures TransactWriteItemsEnsuresPublicly(input, output)
      ensures History.TransactWriteItems == old(History.TransactWriteItems) + [DafnyCallEvent(input, output)]

    predicate UpdateItemEnsuresPublicly(input: UpdateItemInput , output: Result<UpdateItemOutput, Error>)
    // The public method to be called by library consumers
    method UpdateItem ( input: UpdateItemInput )
      returns (output: Result<UpdateItemOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateItem
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateItemEnsuresPublicly(input, output)
      ensures History.UpdateItem == old(History.UpdateItem) + [DafnyCallEvent(input, output)]

  }
  type ErrorMessage = string
  datatype ExecuteStatementInput = | ExecuteStatementInput (
    nameonly Statement: PartiQLStatement ,
    nameonly Parameters: Option<PreparedStatementParameters> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None ,
    nameonly NextToken: Option<PartiQLNextToken> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly Limit: Option<PositiveIntegerObject> := Option.None
  )
  datatype ExecuteStatementOutput = | ExecuteStatementOutput (
    nameonly Items: Option<ItemList> := Option.None ,
    nameonly NextToken: Option<PartiQLNextToken> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None ,
    nameonly LastEvaluatedKey: Option<Key> := Option.None
  )
  datatype ExecuteTransactionInput = | ExecuteTransactionInput (
    nameonly TransactStatements: ParameterizedStatements ,
    nameonly ClientRequestToken: Option<ClientRequestToken> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None
  )
  datatype ExecuteTransactionOutput = | ExecuteTransactionOutput (
    nameonly Responses: Option<ItemResponseList> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None
  )
  type ExpectedAttributeMap = map<AttributeName, ExpectedAttributeValue>
  datatype ExpectedAttributeValue = | ExpectedAttributeValue (
    nameonly Value: Option<AttributeValue> := Option.None ,
    nameonly Exists: Option<BooleanObject> := Option.None ,
    nameonly ComparisonOperator: Option<ComparisonOperator> := Option.None ,
    nameonly AttributeValueList: Option<AttributeValueList> := Option.None
  )
  type ExpressionAttributeNameMap = map<ExpressionAttributeNameVariable, AttributeName>
  type ExpressionAttributeNameVariable = string
  type ExpressionAttributeValueMap = map<ExpressionAttributeValueVariable, AttributeValue>
  type ExpressionAttributeValueVariable = string
  type FilterConditionMap = map<AttributeName, Condition>
  datatype Get = | Get (
    nameonly Key: Key ,
    nameonly TableName: TableName ,
    nameonly ProjectionExpression: Option<ProjectionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None
  )
  datatype GetItemInput = | GetItemInput (
    nameonly TableName: TableName ,
    nameonly Key: Key ,
    nameonly AttributesToGet: Option<AttributeNameList> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ProjectionExpression: Option<ProjectionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None
  )
  datatype GetItemOutput = | GetItemOutput (
    nameonly Item: Option<AttributeMap> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None
  )
  datatype GlobalSecondaryIndex = | GlobalSecondaryIndex (
    nameonly IndexName: IndexName ,
    nameonly KeySchema: KeySchema ,
    nameonly Projection: Projection ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None
  )
  datatype GlobalSecondaryIndexDescription = | GlobalSecondaryIndexDescription (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly KeySchema: Option<KeySchema> := Option.None ,
    nameonly Projection: Option<Projection> := Option.None ,
    nameonly IndexStatus: Option<IndexStatus> := Option.None ,
    nameonly Backfilling: Option<Backfilling> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughputDescription> := Option.None ,
    nameonly IndexSizeBytes: Option<Long> := Option.None ,
    nameonly ItemCount: Option<Long> := Option.None ,
    nameonly IndexArn: Option<String> := Option.None
  )
  type GlobalSecondaryIndexDescriptionList = seq<GlobalSecondaryIndexDescription>
  type GlobalSecondaryIndexList = seq<GlobalSecondaryIndex>
  type IndexName = x: string | IsValid_IndexName(x) witness *
  predicate method IsValid_IndexName(x: string) {
    ( 3 <= |x| <= 255 )
  }
  datatype IndexStatus =
    | CREATING
    | UPDATING
    | DELETING
    | ACTIVE
  type Integer = int32
  type ItemCollectionKeyAttributeMap = map<AttributeName, AttributeValue>
  datatype ItemCollectionMetrics = | ItemCollectionMetrics (
    nameonly ItemCollectionKey: Option<ItemCollectionKeyAttributeMap> := Option.None ,
    nameonly SizeEstimateRangeGB: Option<ItemCollectionSizeEstimateRange> := Option.None
  )
  type ItemCollectionMetricsMultiple = seq<ItemCollectionMetrics>
  type ItemCollectionMetricsPerTable = map<TableName, ItemCollectionMetricsMultiple>
  type ItemCollectionSizeEstimateBound = x: seq<uint8> | IsValid_ItemCollectionSizeEstimateBound(x) witness *
  predicate method IsValid_ItemCollectionSizeEstimateBound(x: seq<uint8>) {
    ( 8 <= |x| <= 8 )
  }
  type ItemCollectionSizeEstimateRange = seq<ItemCollectionSizeEstimateBound>
  type ItemList = seq<AttributeMap>
  datatype ItemResponse = | ItemResponse (
    nameonly Item: Option<AttributeMap> := Option.None
  )
  type ItemResponseList = x: seq<ItemResponse> | IsValid_ItemResponseList(x) witness *
  predicate method IsValid_ItemResponseList(x: seq<ItemResponse>) {
    ( 1 <= |x| <= 25 )
  }
  type Key = map<AttributeName, AttributeValue>
  type KeyConditions = map<AttributeName, Condition>
  type KeyExpression = string
  type KeyList = x: seq<Key> | IsValid_KeyList(x) witness *
  predicate method IsValid_KeyList(x: seq<Key>) {
    ( 1 <= |x| <= 100 )
  }
  datatype KeysAndAttributes = | KeysAndAttributes (
    nameonly Keys: KeyList ,
    nameonly AttributesToGet: Option<AttributeNameList> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None ,
    nameonly ProjectionExpression: Option<ProjectionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None
  )
  type KeySchema = x: seq<KeySchemaElement> | IsValid_KeySchema(x) witness *
  predicate method IsValid_KeySchema(x: seq<KeySchemaElement>) {
    ( 1 <= |x| <= 2 )
  }
  type KeySchemaAttributeName = x: string | IsValid_KeySchemaAttributeName(x) witness *
  predicate method IsValid_KeySchemaAttributeName(x: string) {
    ( 1 <= |x| <= 255 )
  }
  datatype KeySchemaElement = | KeySchemaElement (
    nameonly AttributeName: KeySchemaAttributeName ,
    nameonly KeyType: KeyType
  )
  datatype KeyType =
    | HASH
    | RANGE
  type KMSMasterKeyArn = string
  type KMSMasterKeyId = string
  type ListAttributeValue = seq<AttributeValue>
  datatype LocalSecondaryIndex = | LocalSecondaryIndex (
    nameonly IndexName: IndexName ,
    nameonly KeySchema: KeySchema ,
    nameonly Projection: Projection
  )
  datatype LocalSecondaryIndexDescription = | LocalSecondaryIndexDescription (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly KeySchema: Option<KeySchema> := Option.None ,
    nameonly Projection: Option<Projection> := Option.None ,
    nameonly IndexSizeBytes: Option<Long> := Option.None ,
    nameonly ItemCount: Option<Long> := Option.None ,
    nameonly IndexArn: Option<String> := Option.None
  )
  type LocalSecondaryIndexDescriptionList = seq<LocalSecondaryIndexDescription>
  type LocalSecondaryIndexList = seq<LocalSecondaryIndex>
  type Long = int64
  type MapAttributeValue = map<AttributeName, AttributeValue>
  type NonKeyAttributeName = x: string | IsValid_NonKeyAttributeName(x) witness *
  predicate method IsValid_NonKeyAttributeName(x: string) {
    ( 1 <= |x| <= 255 )
  }
  type NonKeyAttributeNameList = x: seq<NonKeyAttributeName> | IsValid_NonKeyAttributeNameList(x) witness *
  predicate method IsValid_NonKeyAttributeNameList(x: seq<NonKeyAttributeName>) {
    ( 1 <= |x| <= 20 )
  }
  type NonNegativeLongObject = x: int64 | IsValid_NonNegativeLongObject(x) witness *
  predicate method IsValid_NonNegativeLongObject(x: int64) {
    ( 0 <= x  )
  }
  type NullAttributeValue = bool
  type NumberAttributeValue = string
  type NumberSetAttributeValue = seq<NumberAttributeValue>
  datatype ParameterizedStatement = | ParameterizedStatement (
    nameonly Statement: PartiQLStatement ,
    nameonly Parameters: Option<PreparedStatementParameters> := Option.None
  )
  type ParameterizedStatements = x: seq<ParameterizedStatement> | IsValid_ParameterizedStatements(x) witness *
  predicate method IsValid_ParameterizedStatements(x: seq<ParameterizedStatement>) {
    ( 1 <= |x| <= 25 )
  }
  type PartiQLBatchRequest = x: seq<BatchStatementRequest> | IsValid_PartiQLBatchRequest(x) witness *
  predicate method IsValid_PartiQLBatchRequest(x: seq<BatchStatementRequest>) {
    ( 1 <= |x| <= 25 )
  }
  type PartiQLBatchResponse = seq<BatchStatementResponse>
  type PartiQLNextToken = x: string | IsValid_PartiQLNextToken(x) witness *
  predicate method IsValid_PartiQLNextToken(x: string) {
    ( 1 <= |x| <= 32768 )
  }
  type PartiQLStatement = x: string | IsValid_PartiQLStatement(x) witness *
  predicate method IsValid_PartiQLStatement(x: string) {
    ( 1 <= |x| <= 8192 )
  }
  type PositiveIntegerObject = x: int32 | IsValid_PositiveIntegerObject(x) witness *
  predicate method IsValid_PositiveIntegerObject(x: int32) {
    ( 1 <= x  )
  }
  type PositiveLongObject = x: int64 | IsValid_PositiveLongObject(x) witness *
  predicate method IsValid_PositiveLongObject(x: int64) {
    ( 1 <= x  )
  }
  type PreparedStatementParameters = x: seq<AttributeValue> | IsValid_PreparedStatementParameters(x) witness *
  predicate method IsValid_PreparedStatementParameters(x: seq<AttributeValue>) {
    ( 1 <= |x|  )
  }
  datatype Projection = | Projection (
    nameonly ProjectionType: Option<ProjectionType> := Option.None ,
    nameonly NonKeyAttributes: Option<NonKeyAttributeNameList> := Option.None
  )
  type ProjectionExpression = string
  datatype ProjectionType =
    | ALL
    | KEYS_ONLY
    | INCLUDE
  datatype ProvisionedThroughput = | ProvisionedThroughput (
    nameonly ReadCapacityUnits: PositiveLongObject ,
    nameonly WriteCapacityUnits: PositiveLongObject
  )
  datatype ProvisionedThroughputDescription = | ProvisionedThroughputDescription (
    nameonly LastIncreaseDateTime: Option<string> := Option.None ,
    nameonly LastDecreaseDateTime: Option<string> := Option.None ,
    nameonly NumberOfDecreasesToday: Option<PositiveLongObject> := Option.None ,
    nameonly ReadCapacityUnits: Option<NonNegativeLongObject> := Option.None ,
    nameonly WriteCapacityUnits: Option<NonNegativeLongObject> := Option.None
  )
  datatype ProvisionedThroughputOverride = | ProvisionedThroughputOverride (
    nameonly ReadCapacityUnits: Option<PositiveLongObject> := Option.None
  )
  datatype Put = | Put (
    nameonly Item: PutItemInputAttributeMap ,
    nameonly TableName: TableName ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure> := Option.None
  )
  datatype PutItemInput = | PutItemInput (
    nameonly TableName: TableName ,
    nameonly Item: PutItemInputAttributeMap ,
    nameonly Expected: Option<ExpectedAttributeMap> := Option.None ,
    nameonly ReturnValues: Option<ReturnValue> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> := Option.None ,
    nameonly ConditionalOperator: Option<ConditionalOperator> := Option.None ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None
  )
  type PutItemInputAttributeMap = map<AttributeName, AttributeValue>
  datatype PutItemOutput = | PutItemOutput (
    nameonly Attributes: Option<AttributeMap> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None ,
    nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics> := Option.None
  )
  datatype PutRequest = | PutRequest (
    nameonly Item: PutItemInputAttributeMap
  )
  datatype QueryInput = | QueryInput (
    nameonly TableName: TableName ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly Select: Option<Select> := Option.None ,
    nameonly AttributesToGet: Option<AttributeNameList> := Option.None ,
    nameonly Limit: Option<PositiveIntegerObject> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None ,
    nameonly KeyConditions: Option<KeyConditions> := Option.None ,
    nameonly QueryFilter: Option<FilterConditionMap> := Option.None ,
    nameonly ConditionalOperator: Option<ConditionalOperator> := Option.None ,
    nameonly ScanIndexForward: Option<BooleanObject> := Option.None ,
    nameonly ExclusiveStartKey: Option<Key> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ProjectionExpression: Option<ProjectionExpression> := Option.None ,
    nameonly FilterExpression: Option<ConditionExpression> := Option.None ,
    nameonly KeyConditionExpression: Option<KeyExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None
  )
  datatype QueryOutput = | QueryOutput (
    nameonly Items: Option<ItemList> := Option.None ,
    nameonly Count: Option<Integer> := Option.None ,
    nameonly ScannedCount: Option<Integer> := Option.None ,
    nameonly LastEvaluatedKey: Option<Key> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None
  )
  type RegionName = string
  datatype ReplicaDescription = | ReplicaDescription (
    nameonly RegionName: Option<RegionName> := Option.None ,
    nameonly ReplicaStatus: Option<ReplicaStatus> := Option.None ,
    nameonly ReplicaStatusDescription: Option<ReplicaStatusDescription> := Option.None ,
    nameonly ReplicaStatusPercentProgress: Option<ReplicaStatusPercentProgress> := Option.None ,
    nameonly KMSMasterKeyId: Option<KMSMasterKeyId> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexDescriptionList> := Option.None ,
    nameonly ReplicaInaccessibleDateTime: Option<string> := Option.None ,
    nameonly ReplicaTableClassSummary: Option<TableClassSummary> := Option.None
  )
  type ReplicaDescriptionList = seq<ReplicaDescription>
  datatype ReplicaGlobalSecondaryIndexDescription = | ReplicaGlobalSecondaryIndexDescription (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None
  )
  type ReplicaGlobalSecondaryIndexDescriptionList = seq<ReplicaGlobalSecondaryIndexDescription>
  datatype ReplicaStatus =
    | CREATING
    | CREATION_FAILED
    | UPDATING
    | DELETING
    | ACTIVE
    | REGION_DISABLED
    | INACCESSIBLE_ENCRYPTION_CREDENTIALS
  type ReplicaStatusDescription = string
  type ReplicaStatusPercentProgress = string
  type RestoreInProgress = bool
  datatype RestoreSummary = | RestoreSummary (
    nameonly SourceBackupArn: Option<BackupArn> := Option.None ,
    nameonly SourceTableArn: Option<TableArn> := Option.None ,
    nameonly RestoreDateTime: string ,
    nameonly RestoreInProgress: RestoreInProgress
  )
  datatype ReturnConsumedCapacity =
    | INDEXES
    | TOTAL
    | NONE
  datatype ReturnItemCollectionMetrics =
    | SIZE
    | NONE
  datatype ReturnValue =
    | NONE
    | ALL_OLD
    | UPDATED_OLD
    | ALL_NEW
    | UPDATED_NEW
  datatype ReturnValuesOnConditionCheckFailure =
    | ALL_OLD
    | NONE
  datatype ScalarAttributeType =
    | S
    | N
    | B
  datatype ScanInput = | ScanInput (
    nameonly TableName: TableName ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly AttributesToGet: Option<AttributeNameList> := Option.None ,
    nameonly Limit: Option<PositiveIntegerObject> := Option.None ,
    nameonly Select: Option<Select> := Option.None ,
    nameonly ScanFilter: Option<FilterConditionMap> := Option.None ,
    nameonly ConditionalOperator: Option<ConditionalOperator> := Option.None ,
    nameonly ExclusiveStartKey: Option<Key> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly TotalSegments: Option<ScanTotalSegments> := Option.None ,
    nameonly Segment: Option<ScanSegment> := Option.None ,
    nameonly ProjectionExpression: Option<ProjectionExpression> := Option.None ,
    nameonly FilterExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ConsistentRead: Option<ConsistentRead> := Option.None
  )
  datatype ScanOutput = | ScanOutput (
    nameonly Items: Option<ItemList> := Option.None ,
    nameonly Count: Option<Integer> := Option.None ,
    nameonly ScannedCount: Option<Integer> := Option.None ,
    nameonly LastEvaluatedKey: Option<Key> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None
  )
  type ScanSegment = x: int32 | IsValid_ScanSegment(x) witness *
  predicate method IsValid_ScanSegment(x: int32) {
    ( 0 <= x <= 999999 )
  }
  type ScanTotalSegments = x: int32 | IsValid_ScanTotalSegments(x) witness *
  predicate method IsValid_ScanTotalSegments(x: int32) {
    ( 1 <= x <= 1000000 )
  }
  type SecondaryIndexesCapacityMap = map<IndexName, Capacity>
  datatype Select =
    | ALL_ATTRIBUTES
    | ALL_PROJECTED_ATTRIBUTES
    | SPECIFIC_ATTRIBUTES
    | COUNT
  datatype SSEDescription = | SSEDescription (
    nameonly Status: Option<SSEStatus> := Option.None ,
    nameonly SSEType: Option<SSEType> := Option.None ,
    nameonly KMSMasterKeyArn: Option<KMSMasterKeyArn> := Option.None ,
    nameonly InaccessibleEncryptionDateTime: Option<string> := Option.None
  )
  type SSEEnabled = bool
  datatype SSESpecification = | SSESpecification (
    nameonly Enabled: Option<SSEEnabled> := Option.None ,
    nameonly SSEType: Option<SSEType> := Option.None ,
    nameonly KMSMasterKeyId: Option<KMSMasterKeyId> := Option.None
  )
  datatype SSEStatus =
    | ENABLING
    | ENABLED
    | DISABLING
    | DISABLED
    | UPDATING
  datatype SSEType =
    | AES256
    | KMS
  type StreamArn = x: string | IsValid_StreamArn(x) witness *
  predicate method IsValid_StreamArn(x: string) {
    ( 37 <= |x| <= 1024 )
  }
  type StreamEnabled = bool
  datatype StreamSpecification = | StreamSpecification (
    nameonly StreamEnabled: StreamEnabled ,
    nameonly StreamViewType: Option<StreamViewType> := Option.None
  )
  datatype StreamViewType =
    | NEW_IMAGE
    | OLD_IMAGE
    | NEW_AND_OLD_IMAGES
    | KEYS_ONLY
  type String = string
  type StringAttributeValue = string
  type StringSetAttributeValue = seq<StringAttributeValue>
  type TableArn = string
  datatype TableClass =
    | STANDARD
    | STANDARD_INFREQUENT_ACCESS
  datatype TableClassSummary = | TableClassSummary (
    nameonly TableClass: Option<TableClass> := Option.None ,
    nameonly LastUpdateDateTime: Option<string> := Option.None
  )
  datatype TableDescription = | TableDescription (
    nameonly AttributeDefinitions: Option<AttributeDefinitions> := Option.None ,
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly KeySchema: Option<KeySchema> := Option.None ,
    nameonly TableStatus: Option<TableStatus> := Option.None ,
    nameonly CreationDateTime: Option<string> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughputDescription> := Option.None ,
    nameonly TableSizeBytes: Option<Long> := Option.None ,
    nameonly ItemCount: Option<Long> := Option.None ,
    nameonly TableArn: Option<String> := Option.None ,
    nameonly TableId: Option<TableId> := Option.None ,
    nameonly BillingModeSummary: Option<BillingModeSummary> := Option.None ,
    nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexDescriptionList> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexDescriptionList> := Option.None ,
    nameonly StreamSpecification: Option<StreamSpecification> := Option.None ,
    nameonly LatestStreamLabel: Option<String> := Option.None ,
    nameonly LatestStreamArn: Option<StreamArn> := Option.None ,
    nameonly GlobalTableVersion: Option<String> := Option.None ,
    nameonly Replicas: Option<ReplicaDescriptionList> := Option.None ,
    nameonly RestoreSummary: Option<RestoreSummary> := Option.None ,
    nameonly SSEDescription: Option<SSEDescription> := Option.None ,
    nameonly ArchivalSummary: Option<ArchivalSummary> := Option.None ,
    nameonly TableClassSummary: Option<TableClassSummary> := Option.None
  )
  type TableId = string
  type TableName = x: string | IsValid_TableName(x) witness *
  predicate method IsValid_TableName(x: string) {
    ( 3 <= |x| <= 255 )
  }
  datatype TableStatus =
    | CREATING
    | UPDATING
    | DELETING
    | ACTIVE
    | INACCESSIBLE_ENCRYPTION_CREDENTIALS
    | ARCHIVING
    | ARCHIVED
  datatype Tag = | Tag (
    nameonly Key: TagKeyString ,
    nameonly Value: TagValueString
  )
  type TagKeyString = x: string | IsValid_TagKeyString(x) witness *
  predicate method IsValid_TagKeyString(x: string) {
    ( 1 <= |x| <= 128 )
  }
  type TagList = seq<Tag>
  type TagValueString = x: string | IsValid_TagValueString(x) witness *
  predicate method IsValid_TagValueString(x: string) {
    ( 0 <= |x| <= 256 )
  }
  datatype TransactGetItem = | TransactGetItem (
    nameonly Get: Get
  )
  type TransactGetItemList = x: seq<TransactGetItem> | IsValid_TransactGetItemList(x) witness *
  predicate method IsValid_TransactGetItemList(x: seq<TransactGetItem>) {
    ( 1 <= |x| <= 25 )
  }
  datatype TransactGetItemsInput = | TransactGetItemsInput (
    nameonly TransactItems: TransactGetItemList ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None
  )
  datatype TransactGetItemsOutput = | TransactGetItemsOutput (
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None ,
    nameonly Responses: Option<ItemResponseList> := Option.None
  )
  datatype TransactWriteItem = | TransactWriteItem (
    nameonly ConditionCheck: Option<ConditionCheck> := Option.None ,
    nameonly Put: Option<Put> := Option.None ,
    nameonly Delete: Option<Delete> := Option.None ,
    nameonly Update: Option<Update> := Option.None
  )
  type TransactWriteItemList = x: seq<TransactWriteItem> | IsValid_TransactWriteItemList(x) witness *
  predicate method IsValid_TransactWriteItemList(x: seq<TransactWriteItem>) {
    ( 1 <= |x| <= 25 )
  }
  datatype TransactWriteItemsInput = | TransactWriteItemsInput (
    nameonly TransactItems: TransactWriteItemList ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> := Option.None ,
    nameonly ClientRequestToken: Option<ClientRequestToken> := Option.None
  )
  datatype TransactWriteItemsOutput = | TransactWriteItemsOutput (
    nameonly ConsumedCapacity: Option<ConsumedCapacityMultiple> := Option.None ,
    nameonly ItemCollectionMetrics: Option<ItemCollectionMetricsPerTable> := Option.None
  )
  datatype Update = | Update (
    nameonly Key: Key ,
    nameonly UpdateExpression: UpdateExpression ,
    nameonly TableName: TableName ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure> := Option.None
  )
  type UpdateExpression = string
  datatype UpdateItemInput = | UpdateItemInput (
    nameonly TableName: TableName ,
    nameonly Key: Key ,
    nameonly AttributeUpdates: Option<AttributeUpdates> := Option.None ,
    nameonly Expected: Option<ExpectedAttributeMap> := Option.None ,
    nameonly ConditionalOperator: Option<ConditionalOperator> := Option.None ,
    nameonly ReturnValues: Option<ReturnValue> := Option.None ,
    nameonly ReturnConsumedCapacity: Option<ReturnConsumedCapacity> := Option.None ,
    nameonly ReturnItemCollectionMetrics: Option<ReturnItemCollectionMetrics> := Option.None ,
    nameonly UpdateExpression: Option<UpdateExpression> := Option.None ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None
  )
  datatype UpdateItemOutput = | UpdateItemOutput (
    nameonly Attributes: Option<AttributeMap> := Option.None ,
    nameonly ConsumedCapacity: Option<ConsumedCapacity> := Option.None ,
    nameonly ItemCollectionMetrics: Option<ItemCollectionMetrics> := Option.None
  )
  datatype WriteRequest = | WriteRequest (
    nameonly PutRequest: Option<PutRequest> := Option.None ,
    nameonly DeleteRequest: Option<DeleteRequest> := Option.None
  )
  type WriteRequests = x: seq<WriteRequest> | IsValid_WriteRequests(x) witness *
  predicate method IsValid_WriteRequests(x: seq<WriteRequest>) {
    ( 1 <= |x| <= 25 )
  }
  datatype Error =
      // Local Error structures are listed here
    | ConditionalCheckFailedException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | DuplicateItemException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | IdempotentParameterMismatchException (
        nameonly Message: Option<ErrorMessage> := Option.None
      )
    | InternalServerError (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | InvalidEndpointException (
        nameonly Message: Option<String> := Option.None
      )
    | ItemCollectionSizeLimitExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | LimitExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ProvisionedThroughputExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | RequestLimitExceeded (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ResourceInUseException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ResourceNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | TransactionCanceledException (
        nameonly Message: Option<ErrorMessage> := Option.None ,
        nameonly CancellationReasons: Option<CancellationReasonList> := Option.None
      )
    | TransactionConflictException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | TransactionInProgressException (
        nameonly Message: Option<ErrorMessage> := Option.None
      )
      // Any dependent models are listed here


      // The Opaque error, used for native, extern, wrapped or unknown errors
    | Opaque(obj: object, alt_text : string)
  type OpaqueError = e: Error | e.Opaque? witness *
}
abstract module AbstractComAmazonawsDynamodbService {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
  import opened Types = ComAmazonawsDynamodbTypes
  datatype DynamoDBClientConfigType = DynamoDBClientConfigType
  function method DefaultDynamoDBClientConfigType(): DynamoDBClientConfigType
  method {:extern} DynamoDBClient()
    returns (res: Result<IDynamoDBClient, Error>)
    ensures res.Success? ==>
              && fresh(res.value)
              && fresh(res.value.Modifies)
              && fresh(res.value.History)
              && res.value.ValidState()
  // Helper functions for the benefit of native code to create a Success(client) without referring to Dafny internals
  function method CreateSuccessOfClient(client: IDynamoDBClient): Result<IDynamoDBClient, Error> {
    Success(client)
  }
  function method CreateFailureOfError(error: Error): Result<IDynamoDBClient, Error> {
    Failure(error)
  }
}
abstract module AbstractComAmazonawsDynamodbOperations {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
  import opened Types = ComAmazonawsDynamodbTypes
  type InternalConfig
  predicate ValidInternalConfig?(config: InternalConfig)
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  predicate BatchExecuteStatementEnsuresPublicly(input: BatchExecuteStatementInput , output: Result<BatchExecuteStatementOutput, Error>)
  // The private method to be refined by the library developer


  method BatchExecuteStatement ( config: InternalConfig , input: BatchExecuteStatementInput )
    returns (output: Result<BatchExecuteStatementOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures BatchExecuteStatementEnsuresPublicly(input, output)


  predicate BatchGetItemEnsuresPublicly(input: BatchGetItemInput , output: Result<BatchGetItemOutput, Error>)
  // The private method to be refined by the library developer


  method BatchGetItem ( config: InternalConfig , input: BatchGetItemInput )
    returns (output: Result<BatchGetItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures BatchGetItemEnsuresPublicly(input, output)


  predicate BatchWriteItemEnsuresPublicly(input: BatchWriteItemInput , output: Result<BatchWriteItemOutput, Error>)
  // The private method to be refined by the library developer


  method BatchWriteItem ( config: InternalConfig , input: BatchWriteItemInput )
    returns (output: Result<BatchWriteItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures BatchWriteItemEnsuresPublicly(input, output)


  predicate CreateTableEnsuresPublicly(input: CreateTableInput , output: Result<CreateTableOutput, Error>)
  // The private method to be refined by the library developer


  method CreateTable ( config: InternalConfig , input: CreateTableInput )
    returns (output: Result<CreateTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateTableEnsuresPublicly(input, output)


  predicate DeleteItemEnsuresPublicly(input: DeleteItemInput , output: Result<DeleteItemOutput, Error>)
  // The private method to be refined by the library developer


  method DeleteItem ( config: InternalConfig , input: DeleteItemInput )
    returns (output: Result<DeleteItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteItemEnsuresPublicly(input, output)


  predicate DescribeTableEnsuresPublicly(input: DescribeTableInput , output: Result<DescribeTableOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeTable ( config: InternalConfig , input: DescribeTableInput )
    returns (output: Result<DescribeTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeTableEnsuresPublicly(input, output)


  predicate ExecuteStatementEnsuresPublicly(input: ExecuteStatementInput , output: Result<ExecuteStatementOutput, Error>)
  // The private method to be refined by the library developer


  method ExecuteStatement ( config: InternalConfig , input: ExecuteStatementInput )
    returns (output: Result<ExecuteStatementOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ExecuteStatementEnsuresPublicly(input, output)


  predicate ExecuteTransactionEnsuresPublicly(input: ExecuteTransactionInput , output: Result<ExecuteTransactionOutput, Error>)
  // The private method to be refined by the library developer


  method ExecuteTransaction ( config: InternalConfig , input: ExecuteTransactionInput )
    returns (output: Result<ExecuteTransactionOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ExecuteTransactionEnsuresPublicly(input, output)


  predicate GetItemEnsuresPublicly(input: GetItemInput , output: Result<GetItemOutput, Error>)
  // The private method to be refined by the library developer


  method GetItem ( config: InternalConfig , input: GetItemInput )
    returns (output: Result<GetItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GetItemEnsuresPublicly(input, output)


  predicate PutItemEnsuresPublicly(input: PutItemInput , output: Result<PutItemOutput, Error>)
  // The private method to be refined by the library developer


  method PutItem ( config: InternalConfig , input: PutItemInput )
    returns (output: Result<PutItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures PutItemEnsuresPublicly(input, output)


  predicate QueryEnsuresPublicly(input: QueryInput , output: Result<QueryOutput, Error>)
  // The private method to be refined by the library developer


  method Query ( config: InternalConfig , input: QueryInput )
    returns (output: Result<QueryOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures QueryEnsuresPublicly(input, output)


  predicate ScanEnsuresPublicly(input: ScanInput , output: Result<ScanOutput, Error>)
  // The private method to be refined by the library developer


  method Scan ( config: InternalConfig , input: ScanInput )
    returns (output: Result<ScanOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ScanEnsuresPublicly(input, output)


  predicate TransactGetItemsEnsuresPublicly(input: TransactGetItemsInput , output: Result<TransactGetItemsOutput, Error>)
  // The private method to be refined by the library developer


  method TransactGetItems ( config: InternalConfig , input: TransactGetItemsInput )
    returns (output: Result<TransactGetItemsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures TransactGetItemsEnsuresPublicly(input, output)


  predicate TransactWriteItemsEnsuresPublicly(input: TransactWriteItemsInput , output: Result<TransactWriteItemsOutput, Error>)
  // The private method to be refined by the library developer


  method TransactWriteItems ( config: InternalConfig , input: TransactWriteItemsInput )
    returns (output: Result<TransactWriteItemsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures TransactWriteItemsEnsuresPublicly(input, output)


  predicate UpdateItemEnsuresPublicly(input: UpdateItemInput , output: Result<UpdateItemOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateItem ( config: InternalConfig , input: UpdateItemInput )
    returns (output: Result<UpdateItemOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateItemEnsuresPublicly(input, output)
}
