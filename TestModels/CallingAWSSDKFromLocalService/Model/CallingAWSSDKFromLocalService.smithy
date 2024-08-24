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
  operations: [ CallDDB ],
  errors: [ SimpleCallingAWSSDKFromLocalServiceException ],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation CallDDB {
  input: CallDDBInput,
  output: CallDDBOutput,
}

structure CallDDBInput {
  @required
  tableArn: com.amazonaws.dynamodb#TableArn
  MyString: MyString,
}

@length(min: 1, max: 10)
string MyString

structure CallDDBOutput {
  MyString: MyString,
}

@error("client")
structure SimpleCallingAWSSDKFromLocalServiceException {
  @required
  message: String,
}
