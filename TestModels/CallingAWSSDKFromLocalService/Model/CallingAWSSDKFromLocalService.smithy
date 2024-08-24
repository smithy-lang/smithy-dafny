// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.callingawssdkfromlocalservice

use com.amazonaws.dynamodb#DynamoDB_20120810

@aws.polymorph#localService(
  sdkId: "SimpleCallingAWSSDKFromLocalService",
  config: SimpleCallingAWSSDKFromLocalServiceConfig,
)

service SimpleCallingAWSSDKFromLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [ BasicGet ],
  errors: [ ],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation BasicGet {
  input: BasicGetInput,
  output: BasicGetOutput,
}

structure BasicGetInput {
  @required
  item: com.amazonaws.dynamodb#GetItemInput
}

structure BasicGetOutput {
  putItemOutput: com.amazonaws.dynamodb#GetItemOutput
}
