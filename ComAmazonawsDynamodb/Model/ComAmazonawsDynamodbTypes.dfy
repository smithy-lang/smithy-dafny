// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/src/Index.dfy"
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
  datatype AutoScalingPolicyDescription = | AutoScalingPolicyDescription (
    nameonly PolicyName: Option<AutoScalingPolicyName> := Option.None ,
    nameonly TargetTrackingScalingPolicyConfiguration: Option<AutoScalingTargetTrackingScalingPolicyConfigurationDescription> := Option.None
  )
  type AutoScalingPolicyDescriptionList = seq<AutoScalingPolicyDescription>
  type AutoScalingPolicyName = x: string | IsValid_AutoScalingPolicyName(x) witness *
  predicate method IsValid_AutoScalingPolicyName(x: string) {
    ( 1 <= |x| <= 256 )
  }
  datatype AutoScalingPolicyUpdate = | AutoScalingPolicyUpdate (
    nameonly PolicyName: Option<AutoScalingPolicyName> := Option.None ,
    nameonly TargetTrackingScalingPolicyConfiguration: AutoScalingTargetTrackingScalingPolicyConfigurationUpdate
  )
  type AutoScalingRoleArn = x: string | IsValid_AutoScalingRoleArn(x) witness *
  predicate method IsValid_AutoScalingRoleArn(x: string) {
    ( 1 <= |x| <= 1600 )
  }
  datatype AutoScalingSettingsDescription = | AutoScalingSettingsDescription (
    nameonly MinimumUnits: Option<PositiveLongObject> := Option.None ,
    nameonly MaximumUnits: Option<PositiveLongObject> := Option.None ,
    nameonly AutoScalingDisabled: Option<BooleanObject> := Option.None ,
    nameonly AutoScalingRoleArn: Option<String> := Option.None ,
    nameonly ScalingPolicies: Option<AutoScalingPolicyDescriptionList> := Option.None
  )
  datatype AutoScalingSettingsUpdate = | AutoScalingSettingsUpdate (
    nameonly MinimumUnits: Option<PositiveLongObject> := Option.None ,
    nameonly MaximumUnits: Option<PositiveLongObject> := Option.None ,
    nameonly AutoScalingDisabled: Option<BooleanObject> := Option.None ,
    nameonly AutoScalingRoleArn: Option<AutoScalingRoleArn> := Option.None ,
    nameonly ScalingPolicyUpdate: Option<AutoScalingPolicyUpdate> := Option.None
  )
  datatype AutoScalingTargetTrackingScalingPolicyConfigurationDescription = | AutoScalingTargetTrackingScalingPolicyConfigurationDescription (
    nameonly DisableScaleIn: Option<BooleanObject> := Option.None ,
    nameonly ScaleInCooldown: Option<IntegerObject> := Option.None ,
    nameonly ScaleOutCooldown: Option<IntegerObject> := Option.None ,
    nameonly TargetValue: Double
  )
  datatype AutoScalingTargetTrackingScalingPolicyConfigurationUpdate = | AutoScalingTargetTrackingScalingPolicyConfigurationUpdate (
    nameonly DisableScaleIn: Option<BooleanObject> := Option.None ,
    nameonly ScaleInCooldown: Option<IntegerObject> := Option.None ,
    nameonly ScaleOutCooldown: Option<IntegerObject> := Option.None ,
    nameonly TargetValue: Double
  )
  type Backfilling = bool
  type BackupArn = x: string | IsValid_BackupArn(x) witness *
  predicate method IsValid_BackupArn(x: string) {
    ( 37 <= |x| <= 1024 )
  }
  datatype BackupDescription = | BackupDescription (
    nameonly BackupDetails: Option<BackupDetails> := Option.None ,
    nameonly SourceTableDetails: Option<SourceTableDetails> := Option.None ,
    nameonly SourceTableFeatureDetails: Option<SourceTableFeatureDetails> := Option.None
  )
  datatype BackupDetails = | BackupDetails (
    nameonly BackupArn: BackupArn ,
    nameonly BackupName: BackupName ,
    nameonly BackupSizeBytes: Option<BackupSizeBytes> := Option.None ,
    nameonly BackupStatus: BackupStatus ,
    nameonly BackupType: BackupType ,
    nameonly BackupCreationDateTime: string ,
    nameonly BackupExpiryDateTime: Option<string> := Option.None
  )
  type BackupName = x: string | IsValid_BackupName(x) witness *
  predicate method IsValid_BackupName(x: string) {
    ( 3 <= |x| <= 255 )
  }
  type BackupsInputLimit = x: int32 | IsValid_BackupsInputLimit(x) witness *
  predicate method IsValid_BackupsInputLimit(x: int32) {
    ( 1 <= x <= 100 )
  }
  type BackupSizeBytes = x: int64 | IsValid_BackupSizeBytes(x) witness *
  predicate method IsValid_BackupSizeBytes(x: int64) {
    ( 0 <= x  )
  }
  datatype BackupStatus =
    | CREATING
    | DELETED
    | AVAILABLE
  type BackupSummaries = seq<BackupSummary>
  datatype BackupSummary = | BackupSummary (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly TableId: Option<TableId> := Option.None ,
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly BackupArn: Option<BackupArn> := Option.None ,
    nameonly BackupName: Option<BackupName> := Option.None ,
    nameonly BackupCreationDateTime: Option<string> := Option.None ,
    nameonly BackupExpiryDateTime: Option<string> := Option.None ,
    nameonly BackupStatus: Option<BackupStatus> := Option.None ,
    nameonly BackupType: Option<BackupType> := Option.None ,
    nameonly BackupSizeBytes: Option<BackupSizeBytes> := Option.None
  )
  datatype BackupType =
    | USER
    | SYSTEM
    | AWS_BACKUP
  datatype BackupTypeFilter =
    | USER
    | SYSTEM
    | AWS_BACKUP
    | ALL
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
  type BilledSizeBytes = x: int64 | IsValid_BilledSizeBytes(x) witness *
  predicate method IsValid_BilledSizeBytes(x: int64) {
    ( 0 <= x  )
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
  type ClientToken = string
  type CloudWatchLogGroupArn = x: string | IsValid_CloudWatchLogGroupArn(x) witness *
  predicate method IsValid_CloudWatchLogGroupArn(x: string) {
    ( 1 <= |x| <= 1024 )
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
  datatype ContinuousBackupsDescription = | ContinuousBackupsDescription (
    nameonly ContinuousBackupsStatus: ContinuousBackupsStatus ,
    nameonly PointInTimeRecoveryDescription: Option<PointInTimeRecoveryDescription> := Option.None
  )
  datatype ContinuousBackupsStatus =
    | ENABLED
    | DISABLED
  datatype ContributorInsightsAction =
    | ENABLE
    | DISABLE
  type ContributorInsightsRule = string
  type ContributorInsightsRuleList = seq<ContributorInsightsRule>
  datatype ContributorInsightsStatus =
    | ENABLING
    | ENABLED
    | DISABLING
    | DISABLED
    | FAILED
  type ContributorInsightsSummaries = seq<ContributorInsightsSummary>
  datatype ContributorInsightsSummary = | ContributorInsightsSummary (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus> := Option.None
  )
  datatype CreateBackupInput = | CreateBackupInput (
    nameonly TableName: TableName ,
    nameonly BackupName: BackupName
  )
  datatype CreateBackupOutput = | CreateBackupOutput (
    nameonly BackupDetails: Option<BackupDetails> := Option.None
  )
  datatype CreateGlobalSecondaryIndexAction = | CreateGlobalSecondaryIndexAction (
    nameonly IndexName: IndexName ,
    nameonly KeySchema: KeySchema ,
    nameonly Projection: Projection ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None
  )
  datatype CreateGlobalTableInput = | CreateGlobalTableInput (
    nameonly GlobalTableName: TableName ,
    nameonly ReplicationGroup: ReplicaList
  )
  datatype CreateGlobalTableOutput = | CreateGlobalTableOutput (
    nameonly GlobalTableDescription: Option<GlobalTableDescription> := Option.None
  )
  datatype CreateReplicaAction = | CreateReplicaAction (
    nameonly RegionName: RegionName
  )
  datatype CreateReplicationGroupMemberAction = | CreateReplicationGroupMemberAction (
    nameonly RegionName: RegionName ,
    nameonly KMSMasterKeyId: Option<KMSMasterKeyId> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexList> := Option.None ,
    nameonly TableClassOverride: Option<TableClass> := Option.None
  )
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
  type CsvDelimiter = x: string | IsValid_CsvDelimiter(x) witness *
  predicate method IsValid_CsvDelimiter(x: string) {
    ( 1 <= |x| <= 1 )
  }
  type CsvHeader = x: string | IsValid_CsvHeader(x) witness *
  predicate method IsValid_CsvHeader(x: string) {
    ( 1 <= |x| <= 65536 )
  }
  type CsvHeaderList = x: seq<CsvHeader> | IsValid_CsvHeaderList(x) witness *
  predicate method IsValid_CsvHeaderList(x: seq<CsvHeader>) {
    ( 1 <= |x| <= 255 )
  }
  datatype CsvOptions = | CsvOptions (
    nameonly Delimiter: Option<CsvDelimiter> := Option.None ,
    nameonly HeaderList: Option<CsvHeaderList> := Option.None
  )
  datatype Delete = | Delete (
    nameonly Key: Key ,
    nameonly TableName: TableName ,
    nameonly ConditionExpression: Option<ConditionExpression> := Option.None ,
    nameonly ExpressionAttributeNames: Option<ExpressionAttributeNameMap> := Option.None ,
    nameonly ExpressionAttributeValues: Option<ExpressionAttributeValueMap> := Option.None ,
    nameonly ReturnValuesOnConditionCheckFailure: Option<ReturnValuesOnConditionCheckFailure> := Option.None
  )
  datatype DeleteBackupInput = | DeleteBackupInput (
    nameonly BackupArn: BackupArn
  )
  datatype DeleteBackupOutput = | DeleteBackupOutput (
    nameonly BackupDescription: Option<BackupDescription> := Option.None
  )
  datatype DeleteGlobalSecondaryIndexAction = | DeleteGlobalSecondaryIndexAction (
    nameonly IndexName: IndexName
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
  datatype DeleteReplicaAction = | DeleteReplicaAction (
    nameonly RegionName: RegionName
  )
  datatype DeleteReplicationGroupMemberAction = | DeleteReplicationGroupMemberAction (
    nameonly RegionName: RegionName
  )
  datatype DeleteRequest = | DeleteRequest (
    nameonly Key: Key
  )
  datatype DeleteTableInput = | DeleteTableInput (
    nameonly TableName: TableName
  )
  datatype DeleteTableOutput = | DeleteTableOutput (
    nameonly TableDescription: Option<TableDescription> := Option.None
  )
  datatype DescribeBackupInput = | DescribeBackupInput (
    nameonly BackupArn: BackupArn
  )
  datatype DescribeBackupOutput = | DescribeBackupOutput (
    nameonly BackupDescription: Option<BackupDescription> := Option.None
  )
  datatype DescribeContinuousBackupsInput = | DescribeContinuousBackupsInput (
    nameonly TableName: TableName
  )
  datatype DescribeContinuousBackupsOutput = | DescribeContinuousBackupsOutput (
    nameonly ContinuousBackupsDescription: Option<ContinuousBackupsDescription> := Option.None
  )
  datatype DescribeContributorInsightsInput = | DescribeContributorInsightsInput (
    nameonly TableName: TableName ,
    nameonly IndexName: Option<IndexName> := Option.None
  )
  datatype DescribeContributorInsightsOutput = | DescribeContributorInsightsOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ContributorInsightsRuleList: Option<ContributorInsightsRuleList> := Option.None ,
    nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus> := Option.None ,
    nameonly LastUpdateDateTime: Option<string> := Option.None ,
    nameonly FailureException: Option<FailureException> := Option.None
  )
  datatype DescribeEndpointsRequest = | DescribeEndpointsRequest (

                                      )
  datatype DescribeEndpointsResponse = | DescribeEndpointsResponse (
    nameonly Endpoints: Endpoints
  )
  datatype DescribeExportInput = | DescribeExportInput (
    nameonly ExportArn: ExportArn
  )
  datatype DescribeExportOutput = | DescribeExportOutput (
    nameonly ExportDescription: Option<ExportDescription> := Option.None
  )
  datatype DescribeGlobalTableInput = | DescribeGlobalTableInput (
    nameonly GlobalTableName: TableName
  )
  datatype DescribeGlobalTableOutput = | DescribeGlobalTableOutput (
    nameonly GlobalTableDescription: Option<GlobalTableDescription> := Option.None
  )
  datatype DescribeGlobalTableSettingsInput = | DescribeGlobalTableSettingsInput (
    nameonly GlobalTableName: TableName
  )
  datatype DescribeGlobalTableSettingsOutput = | DescribeGlobalTableSettingsOutput (
    nameonly GlobalTableName: Option<TableName> := Option.None ,
    nameonly ReplicaSettings: Option<ReplicaSettingsDescriptionList> := Option.None
  )
  datatype DescribeImportInput = | DescribeImportInput (
    nameonly ImportArn: ImportArn
  )
  datatype DescribeImportOutput = | DescribeImportOutput (
    nameonly ImportTableDescription: ImportTableDescription
  )
  datatype DescribeKinesisStreamingDestinationInput = | DescribeKinesisStreamingDestinationInput (
    nameonly TableName: TableName
  )
  datatype DescribeKinesisStreamingDestinationOutput = | DescribeKinesisStreamingDestinationOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly KinesisDataStreamDestinations: Option<KinesisDataStreamDestinations> := Option.None
  )
  datatype DescribeLimitsInput = | DescribeLimitsInput (

                                 )
  datatype DescribeLimitsOutput = | DescribeLimitsOutput (
    nameonly AccountMaxReadCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly AccountMaxWriteCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly TableMaxReadCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly TableMaxWriteCapacityUnits: Option<PositiveLongObject> := Option.None
  )
  datatype DescribeTableInput = | DescribeTableInput (
    nameonly TableName: TableName
  )
  datatype DescribeTableOutput = | DescribeTableOutput (
    nameonly Table: Option<TableDescription> := Option.None
  )
  datatype DescribeTableReplicaAutoScalingInput = | DescribeTableReplicaAutoScalingInput (
    nameonly TableName: TableName
  )
  datatype DescribeTableReplicaAutoScalingOutput = | DescribeTableReplicaAutoScalingOutput (
    nameonly TableAutoScalingDescription: Option<TableAutoScalingDescription> := Option.None
  )
  datatype DescribeTimeToLiveInput = | DescribeTimeToLiveInput (
    nameonly TableName: TableName
  )
  datatype DescribeTimeToLiveOutput = | DescribeTimeToLiveOutput (
    nameonly TimeToLiveDescription: Option<TimeToLiveDescription> := Option.None
  )
  datatype DestinationStatus =
    | ENABLING
    | ACTIVE
    | DISABLING
    | DISABLED
    | ENABLE_FAILED
  datatype DisableKinesisStreamingDestinationInput = | DisableKinesisStreamingDestinationInput (
    nameonly TableName: TableName ,
    nameonly StreamArn: StreamArn
  )
  datatype DisableKinesisStreamingDestinationOutput = | DisableKinesisStreamingDestinationOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly StreamArn: Option<StreamArn> := Option.None ,
    nameonly DestinationStatus: Option<DestinationStatus> := Option.None
  )
  type Double = x: seq<uint8> | IsValid_Double(x) witness *
  predicate method IsValid_Double(x: seq<uint8>) {
    ( 8 <= |x| <= 8 )
  }
  class IDynamoDBClientCallHistory {
    ghost constructor() {
      BatchExecuteStatement := [];
      BatchGetItem := [];
      BatchWriteItem := [];
      CreateBackup := [];
      CreateGlobalTable := [];
      CreateTable := [];
      DeleteBackup := [];
      DeleteItem := [];
      DeleteTable := [];
      DescribeBackup := [];
      DescribeContinuousBackups := [];
      DescribeContributorInsights := [];
      DescribeEndpoints := [];
      DescribeExport := [];
      DescribeGlobalTable := [];
      DescribeGlobalTableSettings := [];
      DescribeImport := [];
      DescribeKinesisStreamingDestination := [];
      DescribeLimits := [];
      DescribeTable := [];
      DescribeTableReplicaAutoScaling := [];
      DescribeTimeToLive := [];
      DisableKinesisStreamingDestination := [];
      EnableKinesisStreamingDestination := [];
      ExecuteStatement := [];
      ExecuteTransaction := [];
      ExportTableToPointInTime := [];
      GetItem := [];
      ImportTable := [];
      ListBackups := [];
      ListContributorInsights := [];
      ListExports := [];
      ListGlobalTables := [];
      ListImports := [];
      ListTables := [];
      ListTagsOfResource := [];
      PutItem := [];
      Query := [];
      RestoreTableFromBackup := [];
      RestoreTableToPointInTime := [];
      Scan := [];
      TagResource := [];
      TransactGetItems := [];
      TransactWriteItems := [];
      UntagResource := [];
      UpdateContinuousBackups := [];
      UpdateContributorInsights := [];
      UpdateGlobalTable := [];
      UpdateGlobalTableSettings := [];
      UpdateItem := [];
      UpdateTable := [];
      UpdateTableReplicaAutoScaling := [];
      UpdateTimeToLive := [];
    }
    ghost var BatchExecuteStatement: seq<DafnyCallEvent<BatchExecuteStatementInput, Result<BatchExecuteStatementOutput, Error>>>
    ghost var BatchGetItem: seq<DafnyCallEvent<BatchGetItemInput, Result<BatchGetItemOutput, Error>>>
    ghost var BatchWriteItem: seq<DafnyCallEvent<BatchWriteItemInput, Result<BatchWriteItemOutput, Error>>>
    ghost var CreateBackup: seq<DafnyCallEvent<CreateBackupInput, Result<CreateBackupOutput, Error>>>
    ghost var CreateGlobalTable: seq<DafnyCallEvent<CreateGlobalTableInput, Result<CreateGlobalTableOutput, Error>>>
    ghost var CreateTable: seq<DafnyCallEvent<CreateTableInput, Result<CreateTableOutput, Error>>>
    ghost var DeleteBackup: seq<DafnyCallEvent<DeleteBackupInput, Result<DeleteBackupOutput, Error>>>
    ghost var DeleteItem: seq<DafnyCallEvent<DeleteItemInput, Result<DeleteItemOutput, Error>>>
    ghost var DeleteTable: seq<DafnyCallEvent<DeleteTableInput, Result<DeleteTableOutput, Error>>>
    ghost var DescribeBackup: seq<DafnyCallEvent<DescribeBackupInput, Result<DescribeBackupOutput, Error>>>
    ghost var DescribeContinuousBackups: seq<DafnyCallEvent<DescribeContinuousBackupsInput, Result<DescribeContinuousBackupsOutput, Error>>>
    ghost var DescribeContributorInsights: seq<DafnyCallEvent<DescribeContributorInsightsInput, Result<DescribeContributorInsightsOutput, Error>>>
    ghost var DescribeEndpoints: seq<DafnyCallEvent<DescribeEndpointsRequest, Result<DescribeEndpointsResponse, Error>>>
    ghost var DescribeExport: seq<DafnyCallEvent<DescribeExportInput, Result<DescribeExportOutput, Error>>>
    ghost var DescribeGlobalTable: seq<DafnyCallEvent<DescribeGlobalTableInput, Result<DescribeGlobalTableOutput, Error>>>
    ghost var DescribeGlobalTableSettings: seq<DafnyCallEvent<DescribeGlobalTableSettingsInput, Result<DescribeGlobalTableSettingsOutput, Error>>>
    ghost var DescribeImport: seq<DafnyCallEvent<DescribeImportInput, Result<DescribeImportOutput, Error>>>
    ghost var DescribeKinesisStreamingDestination: seq<DafnyCallEvent<DescribeKinesisStreamingDestinationInput, Result<DescribeKinesisStreamingDestinationOutput, Error>>>
    ghost var DescribeLimits: seq<DafnyCallEvent<DescribeLimitsInput, Result<DescribeLimitsOutput, Error>>>
    ghost var DescribeTable: seq<DafnyCallEvent<DescribeTableInput, Result<DescribeTableOutput, Error>>>
    ghost var DescribeTableReplicaAutoScaling: seq<DafnyCallEvent<DescribeTableReplicaAutoScalingInput, Result<DescribeTableReplicaAutoScalingOutput, Error>>>
    ghost var DescribeTimeToLive: seq<DafnyCallEvent<DescribeTimeToLiveInput, Result<DescribeTimeToLiveOutput, Error>>>
    ghost var DisableKinesisStreamingDestination: seq<DafnyCallEvent<DisableKinesisStreamingDestinationInput, Result<DisableKinesisStreamingDestinationOutput, Error>>>
    ghost var EnableKinesisStreamingDestination: seq<DafnyCallEvent<EnableKinesisStreamingDestinationInput, Result<EnableKinesisStreamingDestinationOutput, Error>>>
    ghost var ExecuteStatement: seq<DafnyCallEvent<ExecuteStatementInput, Result<ExecuteStatementOutput, Error>>>
    ghost var ExecuteTransaction: seq<DafnyCallEvent<ExecuteTransactionInput, Result<ExecuteTransactionOutput, Error>>>
    ghost var ExportTableToPointInTime: seq<DafnyCallEvent<ExportTableToPointInTimeInput, Result<ExportTableToPointInTimeOutput, Error>>>
    ghost var GetItem: seq<DafnyCallEvent<GetItemInput, Result<GetItemOutput, Error>>>
    ghost var ImportTable: seq<DafnyCallEvent<ImportTableInput, Result<ImportTableOutput, Error>>>
    ghost var ListBackups: seq<DafnyCallEvent<ListBackupsInput, Result<ListBackupsOutput, Error>>>
    ghost var ListContributorInsights: seq<DafnyCallEvent<ListContributorInsightsInput, Result<ListContributorInsightsOutput, Error>>>
    ghost var ListExports: seq<DafnyCallEvent<ListExportsInput, Result<ListExportsOutput, Error>>>
    ghost var ListGlobalTables: seq<DafnyCallEvent<ListGlobalTablesInput, Result<ListGlobalTablesOutput, Error>>>
    ghost var ListImports: seq<DafnyCallEvent<ListImportsInput, Result<ListImportsOutput, Error>>>
    ghost var ListTables: seq<DafnyCallEvent<ListTablesInput, Result<ListTablesOutput, Error>>>
    ghost var ListTagsOfResource: seq<DafnyCallEvent<ListTagsOfResourceInput, Result<ListTagsOfResourceOutput, Error>>>
    ghost var PutItem: seq<DafnyCallEvent<PutItemInput, Result<PutItemOutput, Error>>>
    ghost var Query: seq<DafnyCallEvent<QueryInput, Result<QueryOutput, Error>>>
    ghost var RestoreTableFromBackup: seq<DafnyCallEvent<RestoreTableFromBackupInput, Result<RestoreTableFromBackupOutput, Error>>>
    ghost var RestoreTableToPointInTime: seq<DafnyCallEvent<RestoreTableToPointInTimeInput, Result<RestoreTableToPointInTimeOutput, Error>>>
    ghost var Scan: seq<DafnyCallEvent<ScanInput, Result<ScanOutput, Error>>>
    ghost var TagResource: seq<DafnyCallEvent<TagResourceInput, Result<(), Error>>>
    ghost var TransactGetItems: seq<DafnyCallEvent<TransactGetItemsInput, Result<TransactGetItemsOutput, Error>>>
    ghost var TransactWriteItems: seq<DafnyCallEvent<TransactWriteItemsInput, Result<TransactWriteItemsOutput, Error>>>
    ghost var UntagResource: seq<DafnyCallEvent<UntagResourceInput, Result<(), Error>>>
    ghost var UpdateContinuousBackups: seq<DafnyCallEvent<UpdateContinuousBackupsInput, Result<UpdateContinuousBackupsOutput, Error>>>
    ghost var UpdateContributorInsights: seq<DafnyCallEvent<UpdateContributorInsightsInput, Result<UpdateContributorInsightsOutput, Error>>>
    ghost var UpdateGlobalTable: seq<DafnyCallEvent<UpdateGlobalTableInput, Result<UpdateGlobalTableOutput, Error>>>
    ghost var UpdateGlobalTableSettings: seq<DafnyCallEvent<UpdateGlobalTableSettingsInput, Result<UpdateGlobalTableSettingsOutput, Error>>>
    ghost var UpdateItem: seq<DafnyCallEvent<UpdateItemInput, Result<UpdateItemOutput, Error>>>
    ghost var UpdateTable: seq<DafnyCallEvent<UpdateTableInput, Result<UpdateTableOutput, Error>>>
    ghost var UpdateTableReplicaAutoScaling: seq<DafnyCallEvent<UpdateTableReplicaAutoScalingInput, Result<UpdateTableReplicaAutoScalingOutput, Error>>>
    ghost var UpdateTimeToLive: seq<DafnyCallEvent<UpdateTimeToLiveInput, Result<UpdateTimeToLiveOutput, Error>>>
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

    predicate CreateBackupEnsuresPublicly(input: CreateBackupInput , output: Result<CreateBackupOutput, Error>)
    // The public method to be called by library consumers
    method CreateBackup ( input: CreateBackupInput )
      returns (output: Result<CreateBackupOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateBackup
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateBackupEnsuresPublicly(input, output)
      ensures History.CreateBackup == old(History.CreateBackup) + [DafnyCallEvent(input, output)]

    predicate CreateGlobalTableEnsuresPublicly(input: CreateGlobalTableInput , output: Result<CreateGlobalTableOutput, Error>)
    // The public method to be called by library consumers
    method CreateGlobalTable ( input: CreateGlobalTableInput )
      returns (output: Result<CreateGlobalTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateGlobalTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateGlobalTableEnsuresPublicly(input, output)
      ensures History.CreateGlobalTable == old(History.CreateGlobalTable) + [DafnyCallEvent(input, output)]

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

    predicate DeleteBackupEnsuresPublicly(input: DeleteBackupInput , output: Result<DeleteBackupOutput, Error>)
    // The public method to be called by library consumers
    method DeleteBackup ( input: DeleteBackupInput )
      returns (output: Result<DeleteBackupOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteBackup
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteBackupEnsuresPublicly(input, output)
      ensures History.DeleteBackup == old(History.DeleteBackup) + [DafnyCallEvent(input, output)]

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

    predicate DeleteTableEnsuresPublicly(input: DeleteTableInput , output: Result<DeleteTableOutput, Error>)
    // The public method to be called by library consumers
    method DeleteTable ( input: DeleteTableInput )
      returns (output: Result<DeleteTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteTableEnsuresPublicly(input, output)
      ensures History.DeleteTable == old(History.DeleteTable) + [DafnyCallEvent(input, output)]

    predicate DescribeBackupEnsuresPublicly(input: DescribeBackupInput , output: Result<DescribeBackupOutput, Error>)
    // The public method to be called by library consumers
    method DescribeBackup ( input: DescribeBackupInput )
      returns (output: Result<DescribeBackupOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeBackup
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeBackupEnsuresPublicly(input, output)
      ensures History.DescribeBackup == old(History.DescribeBackup) + [DafnyCallEvent(input, output)]

    predicate DescribeContinuousBackupsEnsuresPublicly(input: DescribeContinuousBackupsInput , output: Result<DescribeContinuousBackupsOutput, Error>)
    // The public method to be called by library consumers
    method DescribeContinuousBackups ( input: DescribeContinuousBackupsInput )
      returns (output: Result<DescribeContinuousBackupsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeContinuousBackups
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeContinuousBackupsEnsuresPublicly(input, output)
      ensures History.DescribeContinuousBackups == old(History.DescribeContinuousBackups) + [DafnyCallEvent(input, output)]

    predicate DescribeContributorInsightsEnsuresPublicly(input: DescribeContributorInsightsInput , output: Result<DescribeContributorInsightsOutput, Error>)
    // The public method to be called by library consumers
    method DescribeContributorInsights ( input: DescribeContributorInsightsInput )
      returns (output: Result<DescribeContributorInsightsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeContributorInsights
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeContributorInsightsEnsuresPublicly(input, output)
      ensures History.DescribeContributorInsights == old(History.DescribeContributorInsights) + [DafnyCallEvent(input, output)]

    predicate DescribeEndpointsEnsuresPublicly(input: DescribeEndpointsRequest , output: Result<DescribeEndpointsResponse, Error>)
    // The public method to be called by library consumers
    method DescribeEndpoints ( input: DescribeEndpointsRequest )
      returns (output: Result<DescribeEndpointsResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeEndpoints
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeEndpointsEnsuresPublicly(input, output)
      ensures History.DescribeEndpoints == old(History.DescribeEndpoints) + [DafnyCallEvent(input, output)]

    predicate DescribeExportEnsuresPublicly(input: DescribeExportInput , output: Result<DescribeExportOutput, Error>)
    // The public method to be called by library consumers
    method DescribeExport ( input: DescribeExportInput )
      returns (output: Result<DescribeExportOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeExport
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeExportEnsuresPublicly(input, output)
      ensures History.DescribeExport == old(History.DescribeExport) + [DafnyCallEvent(input, output)]

    predicate DescribeGlobalTableEnsuresPublicly(input: DescribeGlobalTableInput , output: Result<DescribeGlobalTableOutput, Error>)
    // The public method to be called by library consumers
    method DescribeGlobalTable ( input: DescribeGlobalTableInput )
      returns (output: Result<DescribeGlobalTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeGlobalTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeGlobalTableEnsuresPublicly(input, output)
      ensures History.DescribeGlobalTable == old(History.DescribeGlobalTable) + [DafnyCallEvent(input, output)]

    predicate DescribeGlobalTableSettingsEnsuresPublicly(input: DescribeGlobalTableSettingsInput , output: Result<DescribeGlobalTableSettingsOutput, Error>)
    // The public method to be called by library consumers
    method DescribeGlobalTableSettings ( input: DescribeGlobalTableSettingsInput )
      returns (output: Result<DescribeGlobalTableSettingsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeGlobalTableSettings
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeGlobalTableSettingsEnsuresPublicly(input, output)
      ensures History.DescribeGlobalTableSettings == old(History.DescribeGlobalTableSettings) + [DafnyCallEvent(input, output)]

    predicate DescribeImportEnsuresPublicly(input: DescribeImportInput , output: Result<DescribeImportOutput, Error>)
    // The public method to be called by library consumers
    method DescribeImport ( input: DescribeImportInput )
      returns (output: Result<DescribeImportOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeImport
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeImportEnsuresPublicly(input, output)
      ensures History.DescribeImport == old(History.DescribeImport) + [DafnyCallEvent(input, output)]

    predicate DescribeKinesisStreamingDestinationEnsuresPublicly(input: DescribeKinesisStreamingDestinationInput , output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
    // The public method to be called by library consumers
    method DescribeKinesisStreamingDestination ( input: DescribeKinesisStreamingDestinationInput )
      returns (output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeKinesisStreamingDestination
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeKinesisStreamingDestinationEnsuresPublicly(input, output)
      ensures History.DescribeKinesisStreamingDestination == old(History.DescribeKinesisStreamingDestination) + [DafnyCallEvent(input, output)]

    predicate DescribeLimitsEnsuresPublicly(input: DescribeLimitsInput , output: Result<DescribeLimitsOutput, Error>)
    // The public method to be called by library consumers
    method DescribeLimits ( input: DescribeLimitsInput )
      returns (output: Result<DescribeLimitsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeLimits
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeLimitsEnsuresPublicly(input, output)
      ensures History.DescribeLimits == old(History.DescribeLimits) + [DafnyCallEvent(input, output)]

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

    predicate DescribeTableReplicaAutoScalingEnsuresPublicly(input: DescribeTableReplicaAutoScalingInput , output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
    // The public method to be called by library consumers
    method DescribeTableReplicaAutoScaling ( input: DescribeTableReplicaAutoScalingInput )
      returns (output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeTableReplicaAutoScaling
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeTableReplicaAutoScalingEnsuresPublicly(input, output)
      ensures History.DescribeTableReplicaAutoScaling == old(History.DescribeTableReplicaAutoScaling) + [DafnyCallEvent(input, output)]

    predicate DescribeTimeToLiveEnsuresPublicly(input: DescribeTimeToLiveInput , output: Result<DescribeTimeToLiveOutput, Error>)
    // The public method to be called by library consumers
    method DescribeTimeToLive ( input: DescribeTimeToLiveInput )
      returns (output: Result<DescribeTimeToLiveOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeTimeToLive
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeTimeToLiveEnsuresPublicly(input, output)
      ensures History.DescribeTimeToLive == old(History.DescribeTimeToLive) + [DafnyCallEvent(input, output)]

    predicate DisableKinesisStreamingDestinationEnsuresPublicly(input: DisableKinesisStreamingDestinationInput , output: Result<DisableKinesisStreamingDestinationOutput, Error>)
    // The public method to be called by library consumers
    method DisableKinesisStreamingDestination ( input: DisableKinesisStreamingDestinationInput )
      returns (output: Result<DisableKinesisStreamingDestinationOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DisableKinesisStreamingDestination
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DisableKinesisStreamingDestinationEnsuresPublicly(input, output)
      ensures History.DisableKinesisStreamingDestination == old(History.DisableKinesisStreamingDestination) + [DafnyCallEvent(input, output)]

    predicate EnableKinesisStreamingDestinationEnsuresPublicly(input: EnableKinesisStreamingDestinationInput , output: Result<EnableKinesisStreamingDestinationOutput, Error>)
    // The public method to be called by library consumers
    method EnableKinesisStreamingDestination ( input: EnableKinesisStreamingDestinationInput )
      returns (output: Result<EnableKinesisStreamingDestinationOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`EnableKinesisStreamingDestination
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures EnableKinesisStreamingDestinationEnsuresPublicly(input, output)
      ensures History.EnableKinesisStreamingDestination == old(History.EnableKinesisStreamingDestination) + [DafnyCallEvent(input, output)]

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

    predicate ExportTableToPointInTimeEnsuresPublicly(input: ExportTableToPointInTimeInput , output: Result<ExportTableToPointInTimeOutput, Error>)
    // The public method to be called by library consumers
    method ExportTableToPointInTime ( input: ExportTableToPointInTimeInput )
      returns (output: Result<ExportTableToPointInTimeOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ExportTableToPointInTime
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ExportTableToPointInTimeEnsuresPublicly(input, output)
      ensures History.ExportTableToPointInTime == old(History.ExportTableToPointInTime) + [DafnyCallEvent(input, output)]

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

    predicate ImportTableEnsuresPublicly(input: ImportTableInput , output: Result<ImportTableOutput, Error>)
    // The public method to be called by library consumers
    method ImportTable ( input: ImportTableInput )
      returns (output: Result<ImportTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ImportTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ImportTableEnsuresPublicly(input, output)
      ensures History.ImportTable == old(History.ImportTable) + [DafnyCallEvent(input, output)]

    predicate ListBackupsEnsuresPublicly(input: ListBackupsInput , output: Result<ListBackupsOutput, Error>)
    // The public method to be called by library consumers
    method ListBackups ( input: ListBackupsInput )
      returns (output: Result<ListBackupsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListBackups
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListBackupsEnsuresPublicly(input, output)
      ensures History.ListBackups == old(History.ListBackups) + [DafnyCallEvent(input, output)]

    predicate ListContributorInsightsEnsuresPublicly(input: ListContributorInsightsInput , output: Result<ListContributorInsightsOutput, Error>)
    // The public method to be called by library consumers
    method ListContributorInsights ( input: ListContributorInsightsInput )
      returns (output: Result<ListContributorInsightsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListContributorInsights
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListContributorInsightsEnsuresPublicly(input, output)
      ensures History.ListContributorInsights == old(History.ListContributorInsights) + [DafnyCallEvent(input, output)]

    predicate ListExportsEnsuresPublicly(input: ListExportsInput , output: Result<ListExportsOutput, Error>)
    // The public method to be called by library consumers
    method ListExports ( input: ListExportsInput )
      returns (output: Result<ListExportsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListExports
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListExportsEnsuresPublicly(input, output)
      ensures History.ListExports == old(History.ListExports) + [DafnyCallEvent(input, output)]

    predicate ListGlobalTablesEnsuresPublicly(input: ListGlobalTablesInput , output: Result<ListGlobalTablesOutput, Error>)
    // The public method to be called by library consumers
    method ListGlobalTables ( input: ListGlobalTablesInput )
      returns (output: Result<ListGlobalTablesOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListGlobalTables
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListGlobalTablesEnsuresPublicly(input, output)
      ensures History.ListGlobalTables == old(History.ListGlobalTables) + [DafnyCallEvent(input, output)]

    predicate ListImportsEnsuresPublicly(input: ListImportsInput , output: Result<ListImportsOutput, Error>)
    // The public method to be called by library consumers
    method ListImports ( input: ListImportsInput )
      returns (output: Result<ListImportsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListImports
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListImportsEnsuresPublicly(input, output)
      ensures History.ListImports == old(History.ListImports) + [DafnyCallEvent(input, output)]

    predicate ListTablesEnsuresPublicly(input: ListTablesInput , output: Result<ListTablesOutput, Error>)
    // The public method to be called by library consumers
    method ListTables ( input: ListTablesInput )
      returns (output: Result<ListTablesOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListTables
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListTablesEnsuresPublicly(input, output)
      ensures History.ListTables == old(History.ListTables) + [DafnyCallEvent(input, output)]

    predicate ListTagsOfResourceEnsuresPublicly(input: ListTagsOfResourceInput , output: Result<ListTagsOfResourceOutput, Error>)
    // The public method to be called by library consumers
    method ListTagsOfResource ( input: ListTagsOfResourceInput )
      returns (output: Result<ListTagsOfResourceOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListTagsOfResource
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListTagsOfResourceEnsuresPublicly(input, output)
      ensures History.ListTagsOfResource == old(History.ListTagsOfResource) + [DafnyCallEvent(input, output)]

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

    predicate RestoreTableFromBackupEnsuresPublicly(input: RestoreTableFromBackupInput , output: Result<RestoreTableFromBackupOutput, Error>)
    // The public method to be called by library consumers
    method RestoreTableFromBackup ( input: RestoreTableFromBackupInput )
      returns (output: Result<RestoreTableFromBackupOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`RestoreTableFromBackup
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures RestoreTableFromBackupEnsuresPublicly(input, output)
      ensures History.RestoreTableFromBackup == old(History.RestoreTableFromBackup) + [DafnyCallEvent(input, output)]

    predicate RestoreTableToPointInTimeEnsuresPublicly(input: RestoreTableToPointInTimeInput , output: Result<RestoreTableToPointInTimeOutput, Error>)
    // The public method to be called by library consumers
    method RestoreTableToPointInTime ( input: RestoreTableToPointInTimeInput )
      returns (output: Result<RestoreTableToPointInTimeOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`RestoreTableToPointInTime
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures RestoreTableToPointInTimeEnsuresPublicly(input, output)
      ensures History.RestoreTableToPointInTime == old(History.RestoreTableToPointInTime) + [DafnyCallEvent(input, output)]

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

    predicate TagResourceEnsuresPublicly(input: TagResourceInput , output: Result<(), Error>)
    // The public method to be called by library consumers
    method TagResource ( input: TagResourceInput )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`TagResource
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures TagResourceEnsuresPublicly(input, output)
      ensures History.TagResource == old(History.TagResource) + [DafnyCallEvent(input, output)]

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

    predicate UntagResourceEnsuresPublicly(input: UntagResourceInput , output: Result<(), Error>)
    // The public method to be called by library consumers
    method UntagResource ( input: UntagResourceInput )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UntagResource
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UntagResourceEnsuresPublicly(input, output)
      ensures History.UntagResource == old(History.UntagResource) + [DafnyCallEvent(input, output)]

    predicate UpdateContinuousBackupsEnsuresPublicly(input: UpdateContinuousBackupsInput , output: Result<UpdateContinuousBackupsOutput, Error>)
    // The public method to be called by library consumers
    method UpdateContinuousBackups ( input: UpdateContinuousBackupsInput )
      returns (output: Result<UpdateContinuousBackupsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateContinuousBackups
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateContinuousBackupsEnsuresPublicly(input, output)
      ensures History.UpdateContinuousBackups == old(History.UpdateContinuousBackups) + [DafnyCallEvent(input, output)]

    predicate UpdateContributorInsightsEnsuresPublicly(input: UpdateContributorInsightsInput , output: Result<UpdateContributorInsightsOutput, Error>)
    // The public method to be called by library consumers
    method UpdateContributorInsights ( input: UpdateContributorInsightsInput )
      returns (output: Result<UpdateContributorInsightsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateContributorInsights
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateContributorInsightsEnsuresPublicly(input, output)
      ensures History.UpdateContributorInsights == old(History.UpdateContributorInsights) + [DafnyCallEvent(input, output)]

    predicate UpdateGlobalTableEnsuresPublicly(input: UpdateGlobalTableInput , output: Result<UpdateGlobalTableOutput, Error>)
    // The public method to be called by library consumers
    method UpdateGlobalTable ( input: UpdateGlobalTableInput )
      returns (output: Result<UpdateGlobalTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateGlobalTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateGlobalTableEnsuresPublicly(input, output)
      ensures History.UpdateGlobalTable == old(History.UpdateGlobalTable) + [DafnyCallEvent(input, output)]

    predicate UpdateGlobalTableSettingsEnsuresPublicly(input: UpdateGlobalTableSettingsInput , output: Result<UpdateGlobalTableSettingsOutput, Error>)
    // The public method to be called by library consumers
    method UpdateGlobalTableSettings ( input: UpdateGlobalTableSettingsInput )
      returns (output: Result<UpdateGlobalTableSettingsOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateGlobalTableSettings
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateGlobalTableSettingsEnsuresPublicly(input, output)
      ensures History.UpdateGlobalTableSettings == old(History.UpdateGlobalTableSettings) + [DafnyCallEvent(input, output)]

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

    predicate UpdateTableEnsuresPublicly(input: UpdateTableInput , output: Result<UpdateTableOutput, Error>)
    // The public method to be called by library consumers
    method UpdateTable ( input: UpdateTableInput )
      returns (output: Result<UpdateTableOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateTable
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateTableEnsuresPublicly(input, output)
      ensures History.UpdateTable == old(History.UpdateTable) + [DafnyCallEvent(input, output)]

    predicate UpdateTableReplicaAutoScalingEnsuresPublicly(input: UpdateTableReplicaAutoScalingInput , output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
    // The public method to be called by library consumers
    method UpdateTableReplicaAutoScaling ( input: UpdateTableReplicaAutoScalingInput )
      returns (output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateTableReplicaAutoScaling
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateTableReplicaAutoScalingEnsuresPublicly(input, output)
      ensures History.UpdateTableReplicaAutoScaling == old(History.UpdateTableReplicaAutoScaling) + [DafnyCallEvent(input, output)]

    predicate UpdateTimeToLiveEnsuresPublicly(input: UpdateTimeToLiveInput , output: Result<UpdateTimeToLiveOutput, Error>)
    // The public method to be called by library consumers
    method UpdateTimeToLive ( input: UpdateTimeToLiveInput )
      returns (output: Result<UpdateTimeToLiveOutput, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateTimeToLive
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateTimeToLiveEnsuresPublicly(input, output)
      ensures History.UpdateTimeToLive == old(History.UpdateTimeToLive) + [DafnyCallEvent(input, output)]

  }
  datatype EnableKinesisStreamingDestinationInput = | EnableKinesisStreamingDestinationInput (
    nameonly TableName: TableName ,
    nameonly StreamArn: StreamArn
  )
  datatype EnableKinesisStreamingDestinationOutput = | EnableKinesisStreamingDestinationOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly StreamArn: Option<StreamArn> := Option.None ,
    nameonly DestinationStatus: Option<DestinationStatus> := Option.None
  )
  datatype Endpoint = | Endpoint (
    nameonly Address: String ,
    nameonly CachePeriodInMinutes: Long
  )
  type Endpoints = seq<Endpoint>
  type ErrorCount = x: int64 | IsValid_ErrorCount(x) witness *
  predicate method IsValid_ErrorCount(x: int64) {
    ( 0 <= x  )
  }
  type ErrorMessage = string
  type ExceptionDescription = string
  type ExceptionName = string
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
  type ExportArn = x: string | IsValid_ExportArn(x) witness *
  predicate method IsValid_ExportArn(x: string) {
    ( 37 <= |x| <= 1024 )
  }
  datatype ExportDescription = | ExportDescription (
    nameonly ExportArn: Option<ExportArn> := Option.None ,
    nameonly ExportStatus: Option<ExportStatus> := Option.None ,
    nameonly StartTime: Option<string> := Option.None ,
    nameonly EndTime: Option<string> := Option.None ,
    nameonly ExportManifest: Option<ExportManifest> := Option.None ,
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly TableId: Option<TableId> := Option.None ,
    nameonly ExportTime: Option<string> := Option.None ,
    nameonly ClientToken: Option<ClientToken> := Option.None ,
    nameonly S3Bucket: Option<S3Bucket> := Option.None ,
    nameonly S3BucketOwner: Option<S3BucketOwner> := Option.None ,
    nameonly S3Prefix: Option<S3Prefix> := Option.None ,
    nameonly S3SseAlgorithm: Option<S3SseAlgorithm> := Option.None ,
    nameonly S3SseKmsKeyId: Option<S3SseKmsKeyId> := Option.None ,
    nameonly FailureCode: Option<FailureCode> := Option.None ,
    nameonly FailureMessage: Option<FailureMessage> := Option.None ,
    nameonly ExportFormat: Option<ExportFormat> := Option.None ,
    nameonly BilledSizeBytes: Option<BilledSizeBytes> := Option.None ,
    nameonly ItemCount: Option<ItemCount> := Option.None
  )
  datatype ExportFormat =
    | DYNAMODB_JSON
    | ION
  type ExportManifest = string
  type ExportNextToken = string
  datatype ExportStatus =
    | IN_PROGRESS
    | COMPLETED
    | FAILED
  type ExportSummaries = seq<ExportSummary>
  datatype ExportSummary = | ExportSummary (
    nameonly ExportArn: Option<ExportArn> := Option.None ,
    nameonly ExportStatus: Option<ExportStatus> := Option.None
  )
  datatype ExportTableToPointInTimeInput = | ExportTableToPointInTimeInput (
    nameonly TableArn: TableArn ,
    nameonly ExportTime: Option<string> := Option.None ,
    nameonly ClientToken: Option<ClientToken> := Option.None ,
    nameonly S3Bucket: S3Bucket ,
    nameonly S3BucketOwner: Option<S3BucketOwner> := Option.None ,
    nameonly S3Prefix: Option<S3Prefix> := Option.None ,
    nameonly S3SseAlgorithm: Option<S3SseAlgorithm> := Option.None ,
    nameonly S3SseKmsKeyId: Option<S3SseKmsKeyId> := Option.None ,
    nameonly ExportFormat: Option<ExportFormat> := Option.None
  )
  datatype ExportTableToPointInTimeOutput = | ExportTableToPointInTimeOutput (
    nameonly ExportDescription: Option<ExportDescription> := Option.None
  )
  type ExpressionAttributeNameMap = map<ExpressionAttributeNameVariable, AttributeName>
  type ExpressionAttributeNameVariable = string
  type ExpressionAttributeValueMap = map<ExpressionAttributeValueVariable, AttributeValue>
  type ExpressionAttributeValueVariable = string
  type FailureCode = string
  datatype FailureException = | FailureException (
    nameonly ExceptionName: Option<ExceptionName> := Option.None ,
    nameonly ExceptionDescription: Option<ExceptionDescription> := Option.None
  )
  type FailureMessage = string
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
  datatype GlobalSecondaryIndexAutoScalingUpdate = | GlobalSecondaryIndexAutoScalingUpdate (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ProvisionedWriteCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate> := Option.None
  )
  type GlobalSecondaryIndexAutoScalingUpdateList = x: seq<GlobalSecondaryIndexAutoScalingUpdate> | IsValid_GlobalSecondaryIndexAutoScalingUpdateList(x) witness *
  predicate method IsValid_GlobalSecondaryIndexAutoScalingUpdateList(x: seq<GlobalSecondaryIndexAutoScalingUpdate>) {
    ( 1 <= |x|  )
  }
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
  type GlobalSecondaryIndexes = seq<GlobalSecondaryIndexInfo>
  datatype GlobalSecondaryIndexInfo = | GlobalSecondaryIndexInfo (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly KeySchema: Option<KeySchema> := Option.None ,
    nameonly Projection: Option<Projection> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None
  )
  type GlobalSecondaryIndexList = seq<GlobalSecondaryIndex>
  datatype GlobalSecondaryIndexUpdate = | GlobalSecondaryIndexUpdate (
    nameonly Update: Option<UpdateGlobalSecondaryIndexAction> := Option.None ,
    nameonly Create: Option<CreateGlobalSecondaryIndexAction> := Option.None ,
    nameonly Delete: Option<DeleteGlobalSecondaryIndexAction> := Option.None
  )
  type GlobalSecondaryIndexUpdateList = seq<GlobalSecondaryIndexUpdate>
  datatype GlobalTable = | GlobalTable (
    nameonly GlobalTableName: Option<TableName> := Option.None ,
    nameonly ReplicationGroup: Option<ReplicaList> := Option.None
  )
  type GlobalTableArnString = string
  datatype GlobalTableDescription = | GlobalTableDescription (
    nameonly ReplicationGroup: Option<ReplicaDescriptionList> := Option.None ,
    nameonly GlobalTableArn: Option<GlobalTableArnString> := Option.None ,
    nameonly CreationDateTime: Option<string> := Option.None ,
    nameonly GlobalTableStatus: Option<GlobalTableStatus> := Option.None ,
    nameonly GlobalTableName: Option<TableName> := Option.None
  )
  datatype GlobalTableGlobalSecondaryIndexSettingsUpdate = | GlobalTableGlobalSecondaryIndexSettingsUpdate (
    nameonly IndexName: IndexName ,
    nameonly ProvisionedWriteCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly ProvisionedWriteCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> := Option.None
  )
  type GlobalTableGlobalSecondaryIndexSettingsUpdateList = x: seq<GlobalTableGlobalSecondaryIndexSettingsUpdate> | IsValid_GlobalTableGlobalSecondaryIndexSettingsUpdateList(x) witness *
  predicate method IsValid_GlobalTableGlobalSecondaryIndexSettingsUpdateList(x: seq<GlobalTableGlobalSecondaryIndexSettingsUpdate>) {
    ( 1 <= |x| <= 20 )
  }
  type GlobalTableList = seq<GlobalTable>
  datatype GlobalTableStatus =
    | CREATING
    | ACTIVE
    | DELETING
    | UPDATING
  type ImportArn = x: string | IsValid_ImportArn(x) witness *
  predicate method IsValid_ImportArn(x: string) {
    ( 37 <= |x| <= 1024 )
  }
  type ImportedItemCount = x: int64 | IsValid_ImportedItemCount(x) witness *
  predicate method IsValid_ImportedItemCount(x: int64) {
    ( 0 <= x  )
  }
  type ImportNextToken = x: string | IsValid_ImportNextToken(x) witness *
  predicate method IsValid_ImportNextToken(x: string) {
    ( 112 <= |x| <= 1024 )
  }
  datatype ImportStatus =
    | IN_PROGRESS
    | COMPLETED
    | CANCELLING
    | CANCELLED
    | FAILED
  datatype ImportSummary = | ImportSummary (
    nameonly ImportArn: Option<ImportArn> := Option.None ,
    nameonly ImportStatus: Option<ImportStatus> := Option.None ,
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly S3BucketSource: Option<S3BucketSource> := Option.None ,
    nameonly CloudWatchLogGroupArn: Option<CloudWatchLogGroupArn> := Option.None ,
    nameonly InputFormat: Option<InputFormat> := Option.None ,
    nameonly StartTime: Option<string> := Option.None ,
    nameonly EndTime: Option<string> := Option.None
  )
  type ImportSummaryList = seq<ImportSummary>
  datatype ImportTableDescription = | ImportTableDescription (
    nameonly ImportArn: Option<ImportArn> := Option.None ,
    nameonly ImportStatus: Option<ImportStatus> := Option.None ,
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly TableId: Option<TableId> := Option.None ,
    nameonly ClientToken: Option<ClientToken> := Option.None ,
    nameonly S3BucketSource: Option<S3BucketSource> := Option.None ,
    nameonly ErrorCount: Option<ErrorCount> := Option.None ,
    nameonly CloudWatchLogGroupArn: Option<CloudWatchLogGroupArn> := Option.None ,
    nameonly InputFormat: Option<InputFormat> := Option.None ,
    nameonly InputFormatOptions: Option<InputFormatOptions> := Option.None ,
    nameonly InputCompressionType: Option<InputCompressionType> := Option.None ,
    nameonly TableCreationParameters: Option<TableCreationParameters> := Option.None ,
    nameonly StartTime: Option<string> := Option.None ,
    nameonly EndTime: Option<string> := Option.None ,
    nameonly ProcessedSizeBytes: Option<Long> := Option.None ,
    nameonly ProcessedItemCount: Option<ProcessedItemCount> := Option.None ,
    nameonly ImportedItemCount: Option<ImportedItemCount> := Option.None ,
    nameonly FailureCode: Option<FailureCode> := Option.None ,
    nameonly FailureMessage: Option<FailureMessage> := Option.None
  )
  datatype ImportTableInput = | ImportTableInput (
    nameonly ClientToken: Option<ClientToken> := Option.None ,
    nameonly S3BucketSource: S3BucketSource ,
    nameonly InputFormat: InputFormat ,
    nameonly InputFormatOptions: Option<InputFormatOptions> := Option.None ,
    nameonly InputCompressionType: Option<InputCompressionType> := Option.None ,
    nameonly TableCreationParameters: TableCreationParameters
  )
  datatype ImportTableOutput = | ImportTableOutput (
    nameonly ImportTableDescription: ImportTableDescription
  )
  type IndexName = x: string | IsValid_IndexName(x) witness *
  predicate method IsValid_IndexName(x: string) {
    ( 3 <= |x| <= 255 )
  }
  datatype IndexStatus =
    | CREATING
    | UPDATING
    | DELETING
    | ACTIVE
  datatype InputCompressionType =
    | GZIP
    | ZSTD
    | NONE
  datatype InputFormat =
    | DYNAMODB_JSON
    | ION
    | CSV
  datatype InputFormatOptions = | InputFormatOptions (
    nameonly Csv: Option<CsvOptions> := Option.None
  )
  type Integer = int32
  type IntegerObject = int32
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
  type ItemCount = x: int64 | IsValid_ItemCount(x) witness *
  predicate method IsValid_ItemCount(x: int64) {
    ( 0 <= x  )
  }
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
  datatype KinesisDataStreamDestination = | KinesisDataStreamDestination (
    nameonly StreamArn: Option<StreamArn> := Option.None ,
    nameonly DestinationStatus: Option<DestinationStatus> := Option.None ,
    nameonly DestinationStatusDescription: Option<String> := Option.None
  )
  type KinesisDataStreamDestinations = seq<KinesisDataStreamDestination>
  datatype KinesisStreamingDestinationInput = | KinesisStreamingDestinationInput (
    nameonly TableName: TableName ,
    nameonly StreamArn: StreamArn
  )
  datatype KinesisStreamingDestinationOutput = | KinesisStreamingDestinationOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly StreamArn: Option<StreamArn> := Option.None ,
    nameonly DestinationStatus: Option<DestinationStatus> := Option.None
  )
  type KMSMasterKeyArn = string
  type KMSMasterKeyId = string
  type ListAttributeValue = seq<AttributeValue>
  datatype ListBackupsInput = | ListBackupsInput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly Limit: Option<BackupsInputLimit> := Option.None ,
    nameonly TimeRangeLowerBound: Option<string> := Option.None ,
    nameonly TimeRangeUpperBound: Option<string> := Option.None ,
    nameonly ExclusiveStartBackupArn: Option<BackupArn> := Option.None ,
    nameonly BackupType: Option<BackupTypeFilter> := Option.None
  )
  datatype ListBackupsOutput = | ListBackupsOutput (
    nameonly BackupSummaries: Option<BackupSummaries> := Option.None ,
    nameonly LastEvaluatedBackupArn: Option<BackupArn> := Option.None
  )
  datatype ListContributorInsightsInput = | ListContributorInsightsInput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly NextToken: Option<NextTokenString> := Option.None ,
    nameonly MaxResults: Option<ListContributorInsightsLimit> := Option.None
  )
  type ListContributorInsightsLimit = x: int32 | IsValid_ListContributorInsightsLimit(x) witness *
  predicate method IsValid_ListContributorInsightsLimit(x: int32) {
    (  x <= 100 )
  }
  datatype ListContributorInsightsOutput = | ListContributorInsightsOutput (
    nameonly ContributorInsightsSummaries: Option<ContributorInsightsSummaries> := Option.None ,
    nameonly NextToken: Option<NextTokenString> := Option.None
  )
  datatype ListExportsInput = | ListExportsInput (
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly MaxResults: Option<ListExportsMaxLimit> := Option.None ,
    nameonly NextToken: Option<ExportNextToken> := Option.None
  )
  type ListExportsMaxLimit = x: int32 | IsValid_ListExportsMaxLimit(x) witness *
  predicate method IsValid_ListExportsMaxLimit(x: int32) {
    ( 1 <= x <= 25 )
  }
  datatype ListExportsOutput = | ListExportsOutput (
    nameonly ExportSummaries: Option<ExportSummaries> := Option.None ,
    nameonly NextToken: Option<ExportNextToken> := Option.None
  )
  datatype ListGlobalTablesInput = | ListGlobalTablesInput (
    nameonly ExclusiveStartGlobalTableName: Option<TableName> := Option.None ,
    nameonly Limit: Option<PositiveIntegerObject> := Option.None ,
    nameonly RegionName: Option<RegionName> := Option.None
  )
  datatype ListGlobalTablesOutput = | ListGlobalTablesOutput (
    nameonly GlobalTables: Option<GlobalTableList> := Option.None ,
    nameonly LastEvaluatedGlobalTableName: Option<TableName> := Option.None
  )
  datatype ListImportsInput = | ListImportsInput (
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly PageSize: Option<ListImportsMaxLimit> := Option.None ,
    nameonly NextToken: Option<ImportNextToken> := Option.None
  )
  type ListImportsMaxLimit = x: int32 | IsValid_ListImportsMaxLimit(x) witness *
  predicate method IsValid_ListImportsMaxLimit(x: int32) {
    ( 1 <= x <= 25 )
  }
  datatype ListImportsOutput = | ListImportsOutput (
    nameonly ImportSummaryList: Option<ImportSummaryList> := Option.None ,
    nameonly NextToken: Option<ImportNextToken> := Option.None
  )
  datatype ListTablesInput = | ListTablesInput (
    nameonly ExclusiveStartTableName: Option<TableName> := Option.None ,
    nameonly Limit: Option<ListTablesInputLimit> := Option.None
  )
  type ListTablesInputLimit = x: int32 | IsValid_ListTablesInputLimit(x) witness *
  predicate method IsValid_ListTablesInputLimit(x: int32) {
    ( 1 <= x <= 100 )
  }
  datatype ListTablesOutput = | ListTablesOutput (
    nameonly TableNames: Option<TableNameList> := Option.None ,
    nameonly LastEvaluatedTableName: Option<TableName> := Option.None
  )
  datatype ListTagsOfResourceInput = | ListTagsOfResourceInput (
    nameonly ResourceArn: ResourceArnString ,
    nameonly NextToken: Option<NextTokenString> := Option.None
  )
  datatype ListTagsOfResourceOutput = | ListTagsOfResourceOutput (
    nameonly Tags: Option<TagList> := Option.None ,
    nameonly NextToken: Option<NextTokenString> := Option.None
  )
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
  type LocalSecondaryIndexes = seq<LocalSecondaryIndexInfo>
  datatype LocalSecondaryIndexInfo = | LocalSecondaryIndexInfo (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly KeySchema: Option<KeySchema> := Option.None ,
    nameonly Projection: Option<Projection> := Option.None
  )
  type LocalSecondaryIndexList = seq<LocalSecondaryIndex>
  type Long = int64
  type MapAttributeValue = map<AttributeName, AttributeValue>
  type NextTokenString = string
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
  datatype PointInTimeRecoveryDescription = | PointInTimeRecoveryDescription (
    nameonly PointInTimeRecoveryStatus: Option<PointInTimeRecoveryStatus> := Option.None ,
    nameonly EarliestRestorableDateTime: Option<string> := Option.None ,
    nameonly LatestRestorableDateTime: Option<string> := Option.None
  )
  datatype PointInTimeRecoverySpecification = | PointInTimeRecoverySpecification (
    nameonly PointInTimeRecoveryEnabled: BooleanObject
  )
  datatype PointInTimeRecoveryStatus =
    | ENABLED
    | DISABLED
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
  type ProcessedItemCount = x: int64 | IsValid_ProcessedItemCount(x) witness *
  predicate method IsValid_ProcessedItemCount(x: int64) {
    ( 0 <= x  )
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
  datatype Replica = | Replica (
    nameonly RegionName: Option<RegionName> := Option.None
  )
  datatype ReplicaAutoScalingDescription = | ReplicaAutoScalingDescription (
    nameonly RegionName: Option<RegionName> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexAutoScalingDescriptionList> := Option.None ,
    nameonly ReplicaProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ReplicaProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ReplicaStatus: Option<ReplicaStatus> := Option.None
  )
  type ReplicaAutoScalingDescriptionList = seq<ReplicaAutoScalingDescription>
  datatype ReplicaAutoScalingUpdate = | ReplicaAutoScalingUpdate (
    nameonly RegionName: RegionName ,
    nameonly ReplicaGlobalSecondaryIndexUpdates: Option<ReplicaGlobalSecondaryIndexAutoScalingUpdateList> := Option.None ,
    nameonly ReplicaProvisionedReadCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate> := Option.None
  )
  type ReplicaAutoScalingUpdateList = x: seq<ReplicaAutoScalingUpdate> | IsValid_ReplicaAutoScalingUpdateList(x) witness *
  predicate method IsValid_ReplicaAutoScalingUpdateList(x: seq<ReplicaAutoScalingUpdate>) {
    ( 1 <= |x|  )
  }
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
  datatype ReplicaGlobalSecondaryIndex = | ReplicaGlobalSecondaryIndex (
    nameonly IndexName: IndexName ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None
  )
  datatype ReplicaGlobalSecondaryIndexAutoScalingDescription = | ReplicaGlobalSecondaryIndexAutoScalingDescription (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly IndexStatus: Option<IndexStatus> := Option.None ,
    nameonly ProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None
  )
  type ReplicaGlobalSecondaryIndexAutoScalingDescriptionList = seq<ReplicaGlobalSecondaryIndexAutoScalingDescription>
  datatype ReplicaGlobalSecondaryIndexAutoScalingUpdate = | ReplicaGlobalSecondaryIndexAutoScalingUpdate (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ProvisionedReadCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate> := Option.None
  )
  type ReplicaGlobalSecondaryIndexAutoScalingUpdateList = seq<ReplicaGlobalSecondaryIndexAutoScalingUpdate>
  datatype ReplicaGlobalSecondaryIndexDescription = | ReplicaGlobalSecondaryIndexDescription (
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None
  )
  type ReplicaGlobalSecondaryIndexDescriptionList = seq<ReplicaGlobalSecondaryIndexDescription>
  type ReplicaGlobalSecondaryIndexList = x: seq<ReplicaGlobalSecondaryIndex> | IsValid_ReplicaGlobalSecondaryIndexList(x) witness *
  predicate method IsValid_ReplicaGlobalSecondaryIndexList(x: seq<ReplicaGlobalSecondaryIndex>) {
    ( 1 <= |x|  )
  }
  datatype ReplicaGlobalSecondaryIndexSettingsDescription = | ReplicaGlobalSecondaryIndexSettingsDescription (
    nameonly IndexName: IndexName ,
    nameonly IndexStatus: Option<IndexStatus> := Option.None ,
    nameonly ProvisionedReadCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly ProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ProvisionedWriteCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly ProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None
  )
  type ReplicaGlobalSecondaryIndexSettingsDescriptionList = seq<ReplicaGlobalSecondaryIndexSettingsDescription>
  datatype ReplicaGlobalSecondaryIndexSettingsUpdate = | ReplicaGlobalSecondaryIndexSettingsUpdate (
    nameonly IndexName: IndexName ,
    nameonly ProvisionedReadCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly ProvisionedReadCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> := Option.None
  )
  type ReplicaGlobalSecondaryIndexSettingsUpdateList = x: seq<ReplicaGlobalSecondaryIndexSettingsUpdate> | IsValid_ReplicaGlobalSecondaryIndexSettingsUpdateList(x) witness *
  predicate method IsValid_ReplicaGlobalSecondaryIndexSettingsUpdateList(x: seq<ReplicaGlobalSecondaryIndexSettingsUpdate>) {
    ( 1 <= |x| <= 20 )
  }
  type ReplicaList = seq<Replica>
  datatype ReplicaSettingsDescription = | ReplicaSettingsDescription (
    nameonly RegionName: RegionName ,
    nameonly ReplicaStatus: Option<ReplicaStatus> := Option.None ,
    nameonly ReplicaBillingModeSummary: Option<BillingModeSummary> := Option.None ,
    nameonly ReplicaProvisionedReadCapacityUnits: Option<NonNegativeLongObject> := Option.None ,
    nameonly ReplicaProvisionedReadCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ReplicaProvisionedWriteCapacityUnits: Option<NonNegativeLongObject> := Option.None ,
    nameonly ReplicaProvisionedWriteCapacityAutoScalingSettings: Option<AutoScalingSettingsDescription> := Option.None ,
    nameonly ReplicaGlobalSecondaryIndexSettings: Option<ReplicaGlobalSecondaryIndexSettingsDescriptionList> := Option.None ,
    nameonly ReplicaTableClassSummary: Option<TableClassSummary> := Option.None
  )
  type ReplicaSettingsDescriptionList = seq<ReplicaSettingsDescription>
  datatype ReplicaSettingsUpdate = | ReplicaSettingsUpdate (
    nameonly RegionName: RegionName ,
    nameonly ReplicaProvisionedReadCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly ReplicaProvisionedReadCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> := Option.None ,
    nameonly ReplicaGlobalSecondaryIndexSettingsUpdate: Option<ReplicaGlobalSecondaryIndexSettingsUpdateList> := Option.None ,
    nameonly ReplicaTableClass: Option<TableClass> := Option.None
  )
  type ReplicaSettingsUpdateList = x: seq<ReplicaSettingsUpdate> | IsValid_ReplicaSettingsUpdateList(x) witness *
  predicate method IsValid_ReplicaSettingsUpdateList(x: seq<ReplicaSettingsUpdate>) {
    ( 1 <= |x| <= 50 )
  }
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
  datatype ReplicationGroupUpdate = | ReplicationGroupUpdate (
    nameonly Create: Option<CreateReplicationGroupMemberAction> := Option.None ,
    nameonly Update: Option<UpdateReplicationGroupMemberAction> := Option.None ,
    nameonly Delete: Option<DeleteReplicationGroupMemberAction> := Option.None
  )
  type ReplicationGroupUpdateList = x: seq<ReplicationGroupUpdate> | IsValid_ReplicationGroupUpdateList(x) witness *
  predicate method IsValid_ReplicationGroupUpdateList(x: seq<ReplicationGroupUpdate>) {
    ( 1 <= |x|  )
  }
  datatype ReplicaUpdate = | ReplicaUpdate (
    nameonly Create: Option<CreateReplicaAction> := Option.None ,
    nameonly Delete: Option<DeleteReplicaAction> := Option.None
  )
  type ReplicaUpdateList = seq<ReplicaUpdate>
  type ResourceArnString = x: string | IsValid_ResourceArnString(x) witness *
  predicate method IsValid_ResourceArnString(x: string) {
    ( 1 <= |x| <= 1283 )
  }
  type RestoreInProgress = bool
  datatype RestoreSummary = | RestoreSummary (
    nameonly SourceBackupArn: Option<BackupArn> := Option.None ,
    nameonly SourceTableArn: Option<TableArn> := Option.None ,
    nameonly RestoreDateTime: string ,
    nameonly RestoreInProgress: RestoreInProgress
  )
  datatype RestoreTableFromBackupInput = | RestoreTableFromBackupInput (
    nameonly TargetTableName: TableName ,
    nameonly BackupArn: BackupArn ,
    nameonly BillingModeOverride: Option<BillingMode> := Option.None ,
    nameonly GlobalSecondaryIndexOverride: Option<GlobalSecondaryIndexList> := Option.None ,
    nameonly LocalSecondaryIndexOverride: Option<LocalSecondaryIndexList> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughput> := Option.None ,
    nameonly SSESpecificationOverride: Option<SSESpecification> := Option.None
  )
  datatype RestoreTableFromBackupOutput = | RestoreTableFromBackupOutput (
    nameonly TableDescription: Option<TableDescription> := Option.None
  )
  datatype RestoreTableToPointInTimeInput = | RestoreTableToPointInTimeInput (
    nameonly SourceTableArn: Option<TableArn> := Option.None ,
    nameonly SourceTableName: Option<TableName> := Option.None ,
    nameonly TargetTableName: TableName ,
    nameonly UseLatestRestorableTime: Option<BooleanObject> := Option.None ,
    nameonly RestoreDateTime: Option<string> := Option.None ,
    nameonly BillingModeOverride: Option<BillingMode> := Option.None ,
    nameonly GlobalSecondaryIndexOverride: Option<GlobalSecondaryIndexList> := Option.None ,
    nameonly LocalSecondaryIndexOverride: Option<LocalSecondaryIndexList> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughput> := Option.None ,
    nameonly SSESpecificationOverride: Option<SSESpecification> := Option.None
  )
  datatype RestoreTableToPointInTimeOutput = | RestoreTableToPointInTimeOutput (
    nameonly TableDescription: Option<TableDescription> := Option.None
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
  type S3Bucket = x: string | IsValid_S3Bucket(x) witness *
  predicate method IsValid_S3Bucket(x: string) {
    ( 0 <= |x| <= 255 )
  }
  type S3BucketOwner = string
  datatype S3BucketSource = | S3BucketSource (
    nameonly S3BucketOwner: Option<S3BucketOwner> := Option.None ,
    nameonly S3Bucket: S3Bucket ,
    nameonly S3KeyPrefix: Option<S3Prefix> := Option.None
  )
  type S3Prefix = x: string | IsValid_S3Prefix(x) witness *
  predicate method IsValid_S3Prefix(x: string) {
    ( 0 <= |x| <= 1024 )
  }
  datatype S3SseAlgorithm =
    | AES256
    | KMS
  type S3SseKmsKeyId = x: string | IsValid_S3SseKmsKeyId(x) witness *
  predicate method IsValid_S3SseKmsKeyId(x: string) {
    ( 1 <= |x| <= 2048 )
  }
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
  datatype SourceTableDetails = | SourceTableDetails (
    nameonly TableName: TableName ,
    nameonly TableId: TableId ,
    nameonly TableArn: Option<TableArn> := Option.None ,
    nameonly TableSizeBytes: Option<Long> := Option.None ,
    nameonly KeySchema: KeySchema ,
    nameonly TableCreationDateTime: string ,
    nameonly ProvisionedThroughput: ProvisionedThroughput ,
    nameonly ItemCount: Option<ItemCount> := Option.None ,
    nameonly BillingMode: Option<BillingMode> := Option.None
  )
  datatype SourceTableFeatureDetails = | SourceTableFeatureDetails (
    nameonly LocalSecondaryIndexes: Option<LocalSecondaryIndexes> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexes> := Option.None ,
    nameonly StreamDescription: Option<StreamSpecification> := Option.None ,
    nameonly TimeToLiveDescription: Option<TimeToLiveDescription> := Option.None ,
    nameonly SSEDescription: Option<SSEDescription> := Option.None
  )
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
  datatype TableAutoScalingDescription = | TableAutoScalingDescription (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly TableStatus: Option<TableStatus> := Option.None ,
    nameonly Replicas: Option<ReplicaAutoScalingDescriptionList> := Option.None
  )
  datatype TableClass =
    | STANDARD
    | STANDARD_INFREQUENT_ACCESS
  datatype TableClassSummary = | TableClassSummary (
    nameonly TableClass: Option<TableClass> := Option.None ,
    nameonly LastUpdateDateTime: Option<string> := Option.None
  )
  datatype TableCreationParameters = | TableCreationParameters (
    nameonly TableName: TableName ,
    nameonly AttributeDefinitions: AttributeDefinitions ,
    nameonly KeySchema: KeySchema ,
    nameonly BillingMode: Option<BillingMode> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None ,
    nameonly SSESpecification: Option<SSESpecification> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<GlobalSecondaryIndexList> := Option.None
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
  type TableNameList = seq<TableName>
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
  type TagKeyList = seq<TagKeyString>
  type TagKeyString = x: string | IsValid_TagKeyString(x) witness *
  predicate method IsValid_TagKeyString(x: string) {
    ( 1 <= |x| <= 128 )
  }
  type TagList = seq<Tag>
  datatype TagResourceInput = | TagResourceInput (
    nameonly ResourceArn: ResourceArnString ,
    nameonly Tags: TagList
  )
  type TagValueString = x: string | IsValid_TagValueString(x) witness *
  predicate method IsValid_TagValueString(x: string) {
    ( 0 <= |x| <= 256 )
  }
  type TimeToLiveAttributeName = x: string | IsValid_TimeToLiveAttributeName(x) witness *
  predicate method IsValid_TimeToLiveAttributeName(x: string) {
    ( 1 <= |x| <= 255 )
  }
  datatype TimeToLiveDescription = | TimeToLiveDescription (
    nameonly TimeToLiveStatus: Option<TimeToLiveStatus> := Option.None ,
    nameonly AttributeName: Option<TimeToLiveAttributeName> := Option.None
  )
  type TimeToLiveEnabled = bool
  datatype TimeToLiveSpecification = | TimeToLiveSpecification (
    nameonly Enabled: TimeToLiveEnabled ,
    nameonly AttributeName: TimeToLiveAttributeName
  )
  datatype TimeToLiveStatus =
    | ENABLING
    | DISABLING
    | ENABLED
    | DISABLED
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
  datatype UntagResourceInput = | UntagResourceInput (
    nameonly ResourceArn: ResourceArnString ,
    nameonly TagKeys: TagKeyList
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
  datatype UpdateContinuousBackupsInput = | UpdateContinuousBackupsInput (
    nameonly TableName: TableName ,
    nameonly PointInTimeRecoverySpecification: PointInTimeRecoverySpecification
  )
  datatype UpdateContinuousBackupsOutput = | UpdateContinuousBackupsOutput (
    nameonly ContinuousBackupsDescription: Option<ContinuousBackupsDescription> := Option.None
  )
  datatype UpdateContributorInsightsInput = | UpdateContributorInsightsInput (
    nameonly TableName: TableName ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ContributorInsightsAction: ContributorInsightsAction
  )
  datatype UpdateContributorInsightsOutput = | UpdateContributorInsightsOutput (
    nameonly TableName: Option<TableName> := Option.None ,
    nameonly IndexName: Option<IndexName> := Option.None ,
    nameonly ContributorInsightsStatus: Option<ContributorInsightsStatus> := Option.None
  )
  type UpdateExpression = string
  datatype UpdateGlobalSecondaryIndexAction = | UpdateGlobalSecondaryIndexAction (
    nameonly IndexName: IndexName ,
    nameonly ProvisionedThroughput: ProvisionedThroughput
  )
  datatype UpdateGlobalTableInput = | UpdateGlobalTableInput (
    nameonly GlobalTableName: TableName ,
    nameonly ReplicaUpdates: ReplicaUpdateList
  )
  datatype UpdateGlobalTableOutput = | UpdateGlobalTableOutput (
    nameonly GlobalTableDescription: Option<GlobalTableDescription> := Option.None
  )
  datatype UpdateGlobalTableSettingsInput = | UpdateGlobalTableSettingsInput (
    nameonly GlobalTableName: TableName ,
    nameonly GlobalTableBillingMode: Option<BillingMode> := Option.None ,
    nameonly GlobalTableProvisionedWriteCapacityUnits: Option<PositiveLongObject> := Option.None ,
    nameonly GlobalTableProvisionedWriteCapacityAutoScalingSettingsUpdate: Option<AutoScalingSettingsUpdate> := Option.None ,
    nameonly GlobalTableGlobalSecondaryIndexSettingsUpdate: Option<GlobalTableGlobalSecondaryIndexSettingsUpdateList> := Option.None ,
    nameonly ReplicaSettingsUpdate: Option<ReplicaSettingsUpdateList> := Option.None
  )
  datatype UpdateGlobalTableSettingsOutput = | UpdateGlobalTableSettingsOutput (
    nameonly GlobalTableName: Option<TableName> := Option.None ,
    nameonly ReplicaSettings: Option<ReplicaSettingsDescriptionList> := Option.None
  )
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
  datatype UpdateReplicationGroupMemberAction = | UpdateReplicationGroupMemberAction (
    nameonly RegionName: RegionName ,
    nameonly KMSMasterKeyId: Option<KMSMasterKeyId> := Option.None ,
    nameonly ProvisionedThroughputOverride: Option<ProvisionedThroughputOverride> := Option.None ,
    nameonly GlobalSecondaryIndexes: Option<ReplicaGlobalSecondaryIndexList> := Option.None ,
    nameonly TableClassOverride: Option<TableClass> := Option.None
  )
  datatype UpdateTableInput = | UpdateTableInput (
    nameonly AttributeDefinitions: Option<AttributeDefinitions> := Option.None ,
    nameonly TableName: TableName ,
    nameonly BillingMode: Option<BillingMode> := Option.None ,
    nameonly ProvisionedThroughput: Option<ProvisionedThroughput> := Option.None ,
    nameonly GlobalSecondaryIndexUpdates: Option<GlobalSecondaryIndexUpdateList> := Option.None ,
    nameonly StreamSpecification: Option<StreamSpecification> := Option.None ,
    nameonly SSESpecification: Option<SSESpecification> := Option.None ,
    nameonly ReplicaUpdates: Option<ReplicationGroupUpdateList> := Option.None ,
    nameonly TableClass: Option<TableClass> := Option.None
  )
  datatype UpdateTableOutput = | UpdateTableOutput (
    nameonly TableDescription: Option<TableDescription> := Option.None
  )
  datatype UpdateTableReplicaAutoScalingInput = | UpdateTableReplicaAutoScalingInput (
    nameonly GlobalSecondaryIndexUpdates: Option<GlobalSecondaryIndexAutoScalingUpdateList> := Option.None ,
    nameonly TableName: TableName ,
    nameonly ProvisionedWriteCapacityAutoScalingUpdate: Option<AutoScalingSettingsUpdate> := Option.None ,
    nameonly ReplicaUpdates: Option<ReplicaAutoScalingUpdateList> := Option.None
  )
  datatype UpdateTableReplicaAutoScalingOutput = | UpdateTableReplicaAutoScalingOutput (
    nameonly TableAutoScalingDescription: Option<TableAutoScalingDescription> := Option.None
  )
  datatype UpdateTimeToLiveInput = | UpdateTimeToLiveInput (
    nameonly TableName: TableName ,
    nameonly TimeToLiveSpecification: TimeToLiveSpecification
  )
  datatype UpdateTimeToLiveOutput = | UpdateTimeToLiveOutput (
    nameonly TimeToLiveSpecification: Option<TimeToLiveSpecification> := Option.None
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
    | BackupInUseException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | BackupNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ConditionalCheckFailedException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ContinuousBackupsUnavailableException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | DuplicateItemException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ExportConflictException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ExportNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | GlobalTableAlreadyExistsException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | GlobalTableNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | IdempotentParameterMismatchException (
        nameonly Message: Option<ErrorMessage> := Option.None
      )
    | ImportConflictException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ImportNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | IndexNotFoundException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | InternalServerError (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | InvalidEndpointException (
        nameonly Message: Option<String> := Option.None
      )
    | InvalidExportTimeException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | InvalidRestoreTimeException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ItemCollectionSizeLimitExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | LimitExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | PointInTimeRecoveryUnavailableException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ProvisionedThroughputExceededException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ReplicaAlreadyExistsException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | ReplicaNotFoundException (
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
    | TableAlreadyExistsException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | TableInUseException (
        nameonly message: Option<ErrorMessage> := Option.None
      )
    | TableNotFoundException (
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
    | Opaque(obj: object)
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


  predicate CreateBackupEnsuresPublicly(input: CreateBackupInput , output: Result<CreateBackupOutput, Error>)
  // The private method to be refined by the library developer


  method CreateBackup ( config: InternalConfig , input: CreateBackupInput )
    returns (output: Result<CreateBackupOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateBackupEnsuresPublicly(input, output)


  predicate CreateGlobalTableEnsuresPublicly(input: CreateGlobalTableInput , output: Result<CreateGlobalTableOutput, Error>)
  // The private method to be refined by the library developer


  method CreateGlobalTable ( config: InternalConfig , input: CreateGlobalTableInput )
    returns (output: Result<CreateGlobalTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateGlobalTableEnsuresPublicly(input, output)


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


  predicate DeleteBackupEnsuresPublicly(input: DeleteBackupInput , output: Result<DeleteBackupOutput, Error>)
  // The private method to be refined by the library developer


  method DeleteBackup ( config: InternalConfig , input: DeleteBackupInput )
    returns (output: Result<DeleteBackupOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteBackupEnsuresPublicly(input, output)


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


  predicate DeleteTableEnsuresPublicly(input: DeleteTableInput , output: Result<DeleteTableOutput, Error>)
  // The private method to be refined by the library developer


  method DeleteTable ( config: InternalConfig , input: DeleteTableInput )
    returns (output: Result<DeleteTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteTableEnsuresPublicly(input, output)


  predicate DescribeBackupEnsuresPublicly(input: DescribeBackupInput , output: Result<DescribeBackupOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeBackup ( config: InternalConfig , input: DescribeBackupInput )
    returns (output: Result<DescribeBackupOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeBackupEnsuresPublicly(input, output)


  predicate DescribeContinuousBackupsEnsuresPublicly(input: DescribeContinuousBackupsInput , output: Result<DescribeContinuousBackupsOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeContinuousBackups ( config: InternalConfig , input: DescribeContinuousBackupsInput )
    returns (output: Result<DescribeContinuousBackupsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeContinuousBackupsEnsuresPublicly(input, output)


  predicate DescribeContributorInsightsEnsuresPublicly(input: DescribeContributorInsightsInput , output: Result<DescribeContributorInsightsOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeContributorInsights ( config: InternalConfig , input: DescribeContributorInsightsInput )
    returns (output: Result<DescribeContributorInsightsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeContributorInsightsEnsuresPublicly(input, output)


  predicate DescribeEndpointsEnsuresPublicly(input: DescribeEndpointsRequest , output: Result<DescribeEndpointsResponse, Error>)
  // The private method to be refined by the library developer


  method DescribeEndpoints ( config: InternalConfig , input: DescribeEndpointsRequest )
    returns (output: Result<DescribeEndpointsResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeEndpointsEnsuresPublicly(input, output)


  predicate DescribeExportEnsuresPublicly(input: DescribeExportInput , output: Result<DescribeExportOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeExport ( config: InternalConfig , input: DescribeExportInput )
    returns (output: Result<DescribeExportOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeExportEnsuresPublicly(input, output)


  predicate DescribeGlobalTableEnsuresPublicly(input: DescribeGlobalTableInput , output: Result<DescribeGlobalTableOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeGlobalTable ( config: InternalConfig , input: DescribeGlobalTableInput )
    returns (output: Result<DescribeGlobalTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeGlobalTableEnsuresPublicly(input, output)


  predicate DescribeGlobalTableSettingsEnsuresPublicly(input: DescribeGlobalTableSettingsInput , output: Result<DescribeGlobalTableSettingsOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeGlobalTableSettings ( config: InternalConfig , input: DescribeGlobalTableSettingsInput )
    returns (output: Result<DescribeGlobalTableSettingsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeGlobalTableSettingsEnsuresPublicly(input, output)


  predicate DescribeImportEnsuresPublicly(input: DescribeImportInput , output: Result<DescribeImportOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeImport ( config: InternalConfig , input: DescribeImportInput )
    returns (output: Result<DescribeImportOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeImportEnsuresPublicly(input, output)


  predicate DescribeKinesisStreamingDestinationEnsuresPublicly(input: DescribeKinesisStreamingDestinationInput , output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeKinesisStreamingDestination ( config: InternalConfig , input: DescribeKinesisStreamingDestinationInput )
    returns (output: Result<DescribeKinesisStreamingDestinationOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeKinesisStreamingDestinationEnsuresPublicly(input, output)


  predicate DescribeLimitsEnsuresPublicly(input: DescribeLimitsInput , output: Result<DescribeLimitsOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeLimits ( config: InternalConfig , input: DescribeLimitsInput )
    returns (output: Result<DescribeLimitsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeLimitsEnsuresPublicly(input, output)


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


  predicate DescribeTableReplicaAutoScalingEnsuresPublicly(input: DescribeTableReplicaAutoScalingInput , output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeTableReplicaAutoScaling ( config: InternalConfig , input: DescribeTableReplicaAutoScalingInput )
    returns (output: Result<DescribeTableReplicaAutoScalingOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeTableReplicaAutoScalingEnsuresPublicly(input, output)


  predicate DescribeTimeToLiveEnsuresPublicly(input: DescribeTimeToLiveInput , output: Result<DescribeTimeToLiveOutput, Error>)
  // The private method to be refined by the library developer


  method DescribeTimeToLive ( config: InternalConfig , input: DescribeTimeToLiveInput )
    returns (output: Result<DescribeTimeToLiveOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeTimeToLiveEnsuresPublicly(input, output)


  predicate DisableKinesisStreamingDestinationEnsuresPublicly(input: DisableKinesisStreamingDestinationInput , output: Result<DisableKinesisStreamingDestinationOutput, Error>)
  // The private method to be refined by the library developer


  method DisableKinesisStreamingDestination ( config: InternalConfig , input: DisableKinesisStreamingDestinationInput )
    returns (output: Result<DisableKinesisStreamingDestinationOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DisableKinesisStreamingDestinationEnsuresPublicly(input, output)


  predicate EnableKinesisStreamingDestinationEnsuresPublicly(input: EnableKinesisStreamingDestinationInput , output: Result<EnableKinesisStreamingDestinationOutput, Error>)
  // The private method to be refined by the library developer


  method EnableKinesisStreamingDestination ( config: InternalConfig , input: EnableKinesisStreamingDestinationInput )
    returns (output: Result<EnableKinesisStreamingDestinationOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures EnableKinesisStreamingDestinationEnsuresPublicly(input, output)


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


  predicate ExportTableToPointInTimeEnsuresPublicly(input: ExportTableToPointInTimeInput , output: Result<ExportTableToPointInTimeOutput, Error>)
  // The private method to be refined by the library developer


  method ExportTableToPointInTime ( config: InternalConfig , input: ExportTableToPointInTimeInput )
    returns (output: Result<ExportTableToPointInTimeOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ExportTableToPointInTimeEnsuresPublicly(input, output)


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


  predicate ImportTableEnsuresPublicly(input: ImportTableInput , output: Result<ImportTableOutput, Error>)
  // The private method to be refined by the library developer


  method ImportTable ( config: InternalConfig , input: ImportTableInput )
    returns (output: Result<ImportTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ImportTableEnsuresPublicly(input, output)


  predicate ListBackupsEnsuresPublicly(input: ListBackupsInput , output: Result<ListBackupsOutput, Error>)
  // The private method to be refined by the library developer


  method ListBackups ( config: InternalConfig , input: ListBackupsInput )
    returns (output: Result<ListBackupsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListBackupsEnsuresPublicly(input, output)


  predicate ListContributorInsightsEnsuresPublicly(input: ListContributorInsightsInput , output: Result<ListContributorInsightsOutput, Error>)
  // The private method to be refined by the library developer


  method ListContributorInsights ( config: InternalConfig , input: ListContributorInsightsInput )
    returns (output: Result<ListContributorInsightsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListContributorInsightsEnsuresPublicly(input, output)


  predicate ListExportsEnsuresPublicly(input: ListExportsInput , output: Result<ListExportsOutput, Error>)
  // The private method to be refined by the library developer


  method ListExports ( config: InternalConfig , input: ListExportsInput )
    returns (output: Result<ListExportsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListExportsEnsuresPublicly(input, output)


  predicate ListGlobalTablesEnsuresPublicly(input: ListGlobalTablesInput , output: Result<ListGlobalTablesOutput, Error>)
  // The private method to be refined by the library developer


  method ListGlobalTables ( config: InternalConfig , input: ListGlobalTablesInput )
    returns (output: Result<ListGlobalTablesOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListGlobalTablesEnsuresPublicly(input, output)


  predicate ListImportsEnsuresPublicly(input: ListImportsInput , output: Result<ListImportsOutput, Error>)
  // The private method to be refined by the library developer


  method ListImports ( config: InternalConfig , input: ListImportsInput )
    returns (output: Result<ListImportsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListImportsEnsuresPublicly(input, output)


  predicate ListTablesEnsuresPublicly(input: ListTablesInput , output: Result<ListTablesOutput, Error>)
  // The private method to be refined by the library developer


  method ListTables ( config: InternalConfig , input: ListTablesInput )
    returns (output: Result<ListTablesOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListTablesEnsuresPublicly(input, output)


  predicate ListTagsOfResourceEnsuresPublicly(input: ListTagsOfResourceInput , output: Result<ListTagsOfResourceOutput, Error>)
  // The private method to be refined by the library developer


  method ListTagsOfResource ( config: InternalConfig , input: ListTagsOfResourceInput )
    returns (output: Result<ListTagsOfResourceOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListTagsOfResourceEnsuresPublicly(input, output)


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


  predicate RestoreTableFromBackupEnsuresPublicly(input: RestoreTableFromBackupInput , output: Result<RestoreTableFromBackupOutput, Error>)
  // The private method to be refined by the library developer


  method RestoreTableFromBackup ( config: InternalConfig , input: RestoreTableFromBackupInput )
    returns (output: Result<RestoreTableFromBackupOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures RestoreTableFromBackupEnsuresPublicly(input, output)


  predicate RestoreTableToPointInTimeEnsuresPublicly(input: RestoreTableToPointInTimeInput , output: Result<RestoreTableToPointInTimeOutput, Error>)
  // The private method to be refined by the library developer


  method RestoreTableToPointInTime ( config: InternalConfig , input: RestoreTableToPointInTimeInput )
    returns (output: Result<RestoreTableToPointInTimeOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures RestoreTableToPointInTimeEnsuresPublicly(input, output)


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


  predicate TagResourceEnsuresPublicly(input: TagResourceInput , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method TagResource ( config: InternalConfig , input: TagResourceInput )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures TagResourceEnsuresPublicly(input, output)


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


  predicate UntagResourceEnsuresPublicly(input: UntagResourceInput , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method UntagResource ( config: InternalConfig , input: UntagResourceInput )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UntagResourceEnsuresPublicly(input, output)


  predicate UpdateContinuousBackupsEnsuresPublicly(input: UpdateContinuousBackupsInput , output: Result<UpdateContinuousBackupsOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateContinuousBackups ( config: InternalConfig , input: UpdateContinuousBackupsInput )
    returns (output: Result<UpdateContinuousBackupsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateContinuousBackupsEnsuresPublicly(input, output)


  predicate UpdateContributorInsightsEnsuresPublicly(input: UpdateContributorInsightsInput , output: Result<UpdateContributorInsightsOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateContributorInsights ( config: InternalConfig , input: UpdateContributorInsightsInput )
    returns (output: Result<UpdateContributorInsightsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateContributorInsightsEnsuresPublicly(input, output)


  predicate UpdateGlobalTableEnsuresPublicly(input: UpdateGlobalTableInput , output: Result<UpdateGlobalTableOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateGlobalTable ( config: InternalConfig , input: UpdateGlobalTableInput )
    returns (output: Result<UpdateGlobalTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateGlobalTableEnsuresPublicly(input, output)


  predicate UpdateGlobalTableSettingsEnsuresPublicly(input: UpdateGlobalTableSettingsInput , output: Result<UpdateGlobalTableSettingsOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateGlobalTableSettings ( config: InternalConfig , input: UpdateGlobalTableSettingsInput )
    returns (output: Result<UpdateGlobalTableSettingsOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateGlobalTableSettingsEnsuresPublicly(input, output)


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


  predicate UpdateTableEnsuresPublicly(input: UpdateTableInput , output: Result<UpdateTableOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateTable ( config: InternalConfig , input: UpdateTableInput )
    returns (output: Result<UpdateTableOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateTableEnsuresPublicly(input, output)


  predicate UpdateTableReplicaAutoScalingEnsuresPublicly(input: UpdateTableReplicaAutoScalingInput , output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateTableReplicaAutoScaling ( config: InternalConfig , input: UpdateTableReplicaAutoScalingInput )
    returns (output: Result<UpdateTableReplicaAutoScalingOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateTableReplicaAutoScalingEnsuresPublicly(input, output)


  predicate UpdateTimeToLiveEnsuresPublicly(input: UpdateTimeToLiveInput , output: Result<UpdateTimeToLiveOutput, Error>)
  // The private method to be refined by the library developer


  method UpdateTimeToLive ( config: InternalConfig , input: UpdateTimeToLiveInput )
    returns (output: Result<UpdateTimeToLiveOutput, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateTimeToLiveEnsuresPublicly(input, output)
}
