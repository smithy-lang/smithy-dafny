// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.constraints

use com.amazonaws.dynamodb#DynamoDB_20120810

@aws.polymorph#localService(
  sdkId: "SimpleCallingAWSSDKFromLocalService",
  config: SimpleCallingAWSSDKFromLocalServiceConfig,
  dependencies: [
    DynamoDB_20120810
  ]
)

service SimpleCallingAWSSDKFromLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [ CallDDB ],
  errors: [],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation CallDDB {
  input: CallDDBInput,
  output: CallDDBOutput,
}

structure CallDDBInput {
}

structure CallDDBOutput {
  @required
  tableArn: com.amazonaws.dynamodb#TableArn
}
