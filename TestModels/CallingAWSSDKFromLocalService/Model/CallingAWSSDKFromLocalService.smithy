// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.callingawssdkfromlocalservice

use aws.polymorph#reference
use com.amazonaws.dynamodb#DynamoDB_20120810
use com.amazonaws.kms#TrentService

// We don't support @default for local services,
// but this model reuses com.amazonaws.dynamodb#Integer.
// Suppressing that warning to let this test model build,
// but this may have impact in other similar models.
// See https://github.com/smithy-lang/smithy-dafny/issues/745.
apply CallDDBScanOutput$itemOutput @suppress(["UnsupportedFeatures"])

@reference(service: DynamoDB_20120810)
structure DdbClientReference {}

@reference(service: TrentService)
structure KmsClientReference {}

@aws.polymorph#localService(
  sdkId: "SimpleCallingawssdkfromlocalservice",
  config: SimpleCallingawssdkfromlocalserviceConfig,
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
                CallDDBGetItem,
                CallDDBPutItem,
                CallKMSEncrypt,
                CallKMSDecrypt,
                CallKMSGenerateDataKey],
  errors: [ SimpleCallingAWSSDKFromLocalServiceException ],
}

structure SimpleCallingawssdkfromlocalserviceConfig {}

operation CallDDBScan {
  input: CallDDBScanInput,
  output: CallDDBScanOutput,
}

structure CallDDBScanInput {
  ddbClient: DdbClientReference,
  @required
  tableArn: com.amazonaws.dynamodb#TableArn
}

structure CallDDBScanOutput {
  itemOutput: com.amazonaws.dynamodb#Integer,
}

operation CallDDBGetItem {
  input: CallDDBGetItemInput,
  output: CallDDBGetItemOutput,
}

structure CallDDBGetItemInput {
  @required
  ddbClient: DdbClientReference,
  @required
  tableArn: com.amazonaws.dynamodb#TableArn,
  @required
  key: com.amazonaws.dynamodb#Key
}

structure CallDDBGetItemOutput {
  itemOutput: com.amazonaws.dynamodb#AttributeMap,
}

operation CallDDBPutItem {
  input: CallDDBPutItemInput,
  output: CallDDBPutItemOutput
}

structure CallDDBPutItemInput {
  @required
  ddbClient: DdbClientReference,
  @required
  tableArn: com.amazonaws.dynamodb#TableArn,
  @required
  attributeMap: com.amazonaws.dynamodb#PutItemInputAttributeMap
  @required
  conditionExpression: com.amazonaws.dynamodb#ConditionExpression
}

structure CallDDBPutItemOutput {

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
  encryptOutput: com.amazonaws.kms#KeyIdType,
}

operation CallKMSDecrypt {
  input: CallKMSDecryptInput,
  output: CallKMSDecryptOutput,
}

structure CallKMSDecryptInput {
  @required
  kmsClient: KmsClientReference,
  @required
  keyId: com.amazonaws.kms#KeyIdType,
  @required
  ciphertextBlob: com.amazonaws.kms#CiphertextType
}

structure CallKMSDecryptOutput {
  KeyIdType: com.amazonaws.kms#KeyIdType,
  Plaintext: com.amazonaws.kms#PlaintextType
}

operation CallKMSGenerateDataKey {
  input: CallKMSGenerateDataKeyInput,
  output: CallKMSGenerateDataKeyOutput,
}

structure CallKMSGenerateDataKeyInput {
  @required
  kmsClient: KmsClientReference,
  @required
  keyId: com.amazonaws.kms#KeyIdType,
  @required
  numberOfBytesType: com.amazonaws.kms#NumberOfBytesType
}

structure CallKMSGenerateDataKeyOutput {
  ciphertextType: com.amazonaws.kms#CiphertextType,
  plaintext: com.amazonaws.kms#PlaintextType,
  keyId: com.amazonaws.kms#KeyIdType
}

@error("client")
structure SimpleCallingAWSSDKFromLocalServiceException {
  @required
  message: String,
}
