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
  operations: [ CallDDBGetItem,
                CallKMSEncrypt],
  errors: [ SimpleCallingAWSSDKFromLocalServiceException ],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation CallDDBGetItem {
  input: CallDDBGetItemInput,
  output: CallDDBGetItemOutput,
}

structure CallDDBGetItemInput {
  @required
  ddbClient: DdbClientReference,
  @required
  itemInput: com.amazonaws.dynamodb#GetItemInput
}

structure CallDDBGetItemOutput {
  @required
  itemOutput: com.amazonaws.dynamodb#GetItemOutput
}

operation CallKMSEncrypt {
  input: CallKMSEncryptInput,
  output: CallKMSEncryptOutput,
}

structure CallKMSEncryptInput {
  @required
  kmsClient: KmsClientReference,
  @required
  encryptInput: com.amazonaws.kms#EncryptRequest
}

structure CallKMSEncryptOutput {
  @required
  encryptOutput: com.amazonaws.kms#EncryptResponse,
}

@error("client")
structure SimpleCallingAWSSDKFromLocalServiceException {
  @required
  message: String,
}