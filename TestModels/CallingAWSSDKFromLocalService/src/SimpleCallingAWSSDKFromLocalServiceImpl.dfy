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
  predicate CallDDBGetKeyEnsuresPublicly(input: CallDDBGetKeyInput, output: Result<CallDDBGetKeyOutput, Error>) {
    true
  }

  predicate CallKMSEncryptEnsuresPublicly(input: CallKMSEncryptInput, output: Result<CallKMSEncryptOutput, Error>) {
    true
  }

  method CallDDBGetKey ( config: InternalConfig,  input: CallDDBGetKeyInput )
    returns (output: Result<CallDDBGetKeyOutput, Error>) {
    var retGetItem := input.ddbClient.GetItem(input.itemInput);
    if retGetItem.Success? {
        return Success(CallDDBGetKeyOutput(itemOutput := retGetItem.value));
    } else {
        return Failure(SimpleCallingAWSSDKFromLocalServiceException(message := retGetItem.error.message.value));
    }
  }
  method CallKMSEncrypt ( config: InternalConfig,  input: CallKMSEncryptInput )
    returns (output: Result<CallKMSEncryptOutput, Error>) {
      var retEncryptResponse := input.kmsClient.Encrypt(input.encryptInput);
      if retEncryptResponse.Success? {
        return Success(CallKMSEncryptOutput(encryptOutput := retEncryptResponse.value));
      } else {
          return Failure(SimpleCallingAWSSDKFromLocalServiceException(message := retEncryptResponse.error.message.value));
      }
  }
}