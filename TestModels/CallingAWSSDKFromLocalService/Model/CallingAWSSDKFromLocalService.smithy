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
    TrentService
  ]
)

service SimpleCallingAWSSDKFromLocalService {
  version: "2021-11-01",
  resources: [],
  operations: [ 
                CallDDBScan,
                CallKMSEncrypt],
  errors: [ SimpleCallingAWSSDKFromLocalServiceException ],
}

structure SimpleCallingAWSSDKFromLocalServiceConfig {}

operation CallDDBScan {
  input: CallDDBScanInput,
  output: CallDDBScanOutput,
}

structure CallDDBScanInput {
  @required
  ddbClient: DdbClientReference,
  @required
  tableArn: com.amazonaws.dynamodb#TableArn
}

structure CallDDBScanOutput {
  @required
  itemOutput: com.amazonaws.dynamodb#Integer,
}

operation CallKMSEncrypt {
  input: CallKMSEncryptInput,
  output: CallKMSEncryptOutput,
}

structure CallKMSEncryptInput {
  @required
  kmsClient: KmsClientReference,
  @required
  keyId: com.amazonaws.kms#KeyIdType,
  @required
  plaintext: com.amazonaws.kms#PlaintextType
}

structure CallKMSEncryptOutput {
  @required
  encryptOutput: com.amazonaws.kms#KeyIdType,
}

@error("client")
structure SimpleCallingAWSSDKFromLocalServiceException {
  @required
  message: String,
}
