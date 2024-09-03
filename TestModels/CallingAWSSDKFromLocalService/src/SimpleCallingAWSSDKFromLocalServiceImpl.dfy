// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingAWSSDKFromLocalServiceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
  import ComAmazonawsDynamodbTypes
  import ComAmazonawsKmsTypes
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate CallDDBGetItemEnsuresPublicly(input: CallDDBGetItemInput, output: Result<CallDDBGetItemOutput, Error>) {
    true
  }

  predicate CallKMSEncryptEnsuresPublicly(input: CallKMSEncryptInput, output: Result<CallKMSEncryptOutput, Error>) {
    true
  }

  method CallDDBGetItem ( config: InternalConfig,  input: CallDDBGetItemInput )
    returns (output: Result<CallDDBGetItemOutput, Error>) {
    var retGetItem := input.ddbClient.GetItem(input.itemInput);
    if retGetItem.Success? {
      return Success(CallDDBGetItemOutput(itemOutput := retGetItem.value));
    } else {
      return Failure(ComAmazonawsDynamodb(retGetItem.error));
    }
  }
  method CallKMSEncrypt ( config: InternalConfig,  input: CallKMSEncryptInput )
    returns (output: Result<CallKMSEncryptOutput, Error>) {
      var retEncryptResponse := input.kmsClient.Encrypt(input.encryptInput);
      if retEncryptResponse.Success? {
        return Success(CallKMSEncryptOutput(encryptOutput := retEncryptResponse.value));
      } else {
          return Failure(ComAmazonawsKms(retEncryptResponse.error));
      }
  }
}