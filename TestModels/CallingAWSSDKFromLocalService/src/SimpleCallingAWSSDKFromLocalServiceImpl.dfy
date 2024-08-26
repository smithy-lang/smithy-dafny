// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingAWSSDKFromLocalServiceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
  import DDB = ComAmazonawsDynamodbTypes
  import DDBOperations =  Com.Amazonaws.Dynamodb
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate CallDDBEnsuresPublicly(input: CallDDBInput, output: Result<CallDDBOutput, Error>) {
    true
  }

  predicate CallKMSEnsuresPublicly(input: CallDDBInput, output: Result<CallDDBOutput, Error>) {
    true
  }

  method CallDDB ( config: InternalConfig,  input: CallDDBInput )
    returns (output: Result<CallDDBOutput, Error>) {
    return Success(CallDDBOutput(ddbClient := input.ddbClient));
  }
  method CallKMS ( config: InternalConfig,  input: CallKMSInput )
    returns (output: Result<CallKMSOutput, Error>) {
    return Success(CallKMSOutput(kmsClient := input.kmsClient));
  }
}