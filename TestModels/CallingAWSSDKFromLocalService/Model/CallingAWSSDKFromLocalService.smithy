// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.callingawssdkfromlocalservice

use aws.polymorph#reference
use com.amazonaws.dynamodb#DynamoDB_20120810
use com.amazonaws.kms#TrentService


@reference(service: DynamoDB_20120810)
structure DdbClientReference {}

@reference(service: TrentService)
structure KmsClientReference {}

@aws.polymorph#localService(
  sdkId: "SimpleCallingAWSSDKFromLocalService",
  config: SimpleCallingAWSSDKFromLocalServiceConfig,
  dependencies: [
    DynamoDB_20120810,
  ]
)

service SimpleCallingAWSSDKFromLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [ CallDDB,
                CallKMS
             ],
  errors: [ ],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation CallDDB {
  input: CallDDBInput,
  output: CallDDBOutput,
}

structure CallDDBInput {
  @required
  ddbClient: DdbClientReference,
}

structure CallDDBOutput {
  @required
  ddbClient: DdbClientReference,
}

operation CallKMS {
  input: CallKMSInput,
  output: CallKMSOutput,
}

structure CallKMSInput {
  @required
  kmsClient: KmsClientReference,
}

structure CallKMSOutput {
  @required
  kmsClient: KmsClientReference,
}