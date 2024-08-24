// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingAWSSDKFromLocalServiceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
  import ComAmazonawsDynamodbTypes
  import DDBOperations =  Com.Amazonaws.Dynamodb
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate BasicGetEnsuresPublicly(input: BasicGetInput, output: Result<BasicGetOutput, Error>) {
    true
  }

  method BasicGet ( config: InternalConfig,  input: BasicGetInput )
    returns (output: Result<BasicGetOutput, Error>) {
    var client : ComAmazonawsDynamodbTypes.IDynamoDBClient;
    var maybeDdbClient := DDBOperations.DynamoDBClient();
    client :- expect maybeDdbClient;
    var ret := client.GetItem(input.item);
    return Success(BasicGetOutput(putItemOutput := Some(ret.value)));
  }
}