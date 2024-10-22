// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingAWSSDKFromLocalServiceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
  import ComAmazonawsKmsTypes
  import Com.Amazonaws.Kms
  import Com.Amazonaws.Dynamodb

  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate CallDDBScanEnsuresPublicly(input: CallDDBScanInput, output: Result<CallDDBScanOutput, Error>) {
    true
  }

  predicate CallKMSEncryptEnsuresPublicly(input: CallKMSEncryptInput, output: Result<CallKMSEncryptOutput, Error>) {
    true
  }

  method CallDDBScan ( config: InternalConfig,  input: CallDDBScanInput )
    returns (output: Result<CallDDBScanOutput, Error>) {
    var ScanInput := Dynamodb.Types.ScanInput(
      TableName := input.tableArn
    );
    var retScan := input.ddbClient.Scan(ScanInput);
    if retScan.Success? {
      return Success(CallDDBScanOutput(itemOutput := retScan.value.Count.UnwrapOr(-1)));
    } else {
      return Failure(ComAmazonawsDynamodb(retScan.error));
    }
  }
  method CallKMSEncrypt ( config: InternalConfig,  input: CallKMSEncryptInput )
    returns (output: Result<CallKMSEncryptOutput, Error>) {
    var encryptInput := Kms.Types.EncryptRequest(
      KeyId := input.keyId,
      Plaintext := input.plaintext,
      EncryptionContext := Wrappers.None,
      GrantTokens := Wrappers.None,
      EncryptionAlgorithm := Wrappers.None
    );
    var retEncryptResponse := input.kmsClient.Encrypt(encryptInput);
    if retEncryptResponse.Success? {
      return Success(CallKMSEncryptOutput(encryptOutput := retEncryptResponse.value.KeyId.UnwrapOr("")));
    } else {
      return Failure(Types.ComAmazonawsKms(retEncryptResponse.error));
    }
  }
}
