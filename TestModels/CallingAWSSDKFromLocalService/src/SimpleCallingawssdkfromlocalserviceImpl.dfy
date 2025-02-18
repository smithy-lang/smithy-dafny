// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingawssdkfromlocalserviceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
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

  predicate CallDDBGetItemEnsuresPublicly(input: CallDDBGetItemInput, output: Result<CallDDBGetItemOutput, Error>) {
    true
  }

  predicate CallDDBPutItemEnsuresPublicly(input: CallDDBPutItemInput, output: Result<CallDDBPutItemOutput, Error>) {
    true
  }

  predicate CallKMSEncryptEnsuresPublicly(input: CallKMSEncryptInput, output: Result<CallKMSEncryptOutput, Error>) {
    true
  }

  predicate CallKMSDecryptEnsuresPublicly(input: CallKMSDecryptInput, output: Result<CallKMSDecryptOutput, Error>) {
    true
  }

  predicate CallKMSGenerateDataKeyEnsuresPublicly(input: CallKMSGenerateDataKeyInput, output: Result<CallKMSGenerateDataKeyOutput, Error>) {
    true
  }

  method CallDDBScan ( config: InternalConfig,  input: CallDDBScanInput )
    returns (output: Result<CallDDBScanOutput, Error>) {
    var ScanInput := Dynamodb.Types.ScanInput(
      TableName := input.tableArn
    );
    expect input.ddbClient.Some?;
    var retScan := input.ddbClient.value.Scan(ScanInput);
    if retScan.Success? {
      return Success(CallDDBScanOutput(itemOutput := retScan.value.Count));
    } else {
      return Failure(ComAmazonawsDynamodb(retScan.error));
    }
  }

  method CallDDBGetItem ( config: InternalConfig,  input: CallDDBGetItemInput )
    returns (output: Result<CallDDBGetItemOutput, Error>) {
    var GetItemInput := Dynamodb.Types.GetItemInput(
      TableName := input.tableArn,
      Key := input.key
    );
    var retGetItem := input.ddbClient.GetItem(GetItemInput);
    var emptyMap : Dynamodb.Types.AttributeMap := map[];
    if retGetItem.Success? {
      return Success(CallDDBGetItemOutput(itemOutput := retGetItem.value.Item));
    } else {
      return Failure(ComAmazonawsDynamodb(retGetItem.error));
    }
  }

  method CallDDBPutItem ( config: InternalConfig,  input: CallDDBPutItemInput )
    returns (output: Result<CallDDBPutItemOutput, Error>) {
    var PutItemInput := Dynamodb.Types.PutItemInput(
      TableName := input.tableArn,
      Item := input.attributeMap,
      ConditionExpression := Wrappers.Some(input.conditionExpression)
    );
    var retPutItem := input.ddbClient.PutItem(PutItemInput);
    var emptyMap : Dynamodb.Types.AttributeMap := map[];
    if retPutItem.Success? {
      return Success(CallDDBPutItemOutput());
    } else {
      return Failure(ComAmazonawsDynamodb(retPutItem.error));
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
      return Success(CallKMSEncryptOutput(encryptOutput := retEncryptResponse.value.KeyId));
    } else {
      return Failure(Types.ComAmazonawsKms(retEncryptResponse.error));
    }
  }

  method CallKMSDecrypt ( config: InternalConfig,  input: CallKMSDecryptInput )
    returns (output: Result<CallKMSDecryptOutput, Error>) {
    var decryptInput := Kms.Types.DecryptRequest(
      CiphertextBlob := input.ciphertextBlob,
      KeyId := Wrappers.Some(input.keyId)
    );
    var retDecryptResponse := input.kmsClient.Decrypt(decryptInput);
    if retDecryptResponse.Success? {
      return Success(CallKMSDecryptOutput(KeyIdType := retDecryptResponse.value.KeyId, Plaintext := retDecryptResponse.value.Plaintext));
    } else {
      return Failure(Types.ComAmazonawsKms(retDecryptResponse.error));
    }
  }

  method CallKMSGenerateDataKey ( config: InternalConfig , input: CallKMSGenerateDataKeyInput )
    returns (output: Result<CallKMSGenerateDataKeyOutput, Error>) {
    var GenerateDataKeyInput := Kms.Types.GenerateDataKeyRequest(
      KeyId := input.keyId,
      NumberOfBytes := Wrappers.Some(input.numberOfBytesType)
    );
    var retResponse := input.kmsClient.GenerateDataKey(GenerateDataKeyInput);
    if retResponse.Success? {
      return Success(CallKMSGenerateDataKeyOutput(ciphertextType := retResponse.value.CiphertextBlob, plaintext := retResponse.value.Plaintext, keyId := retResponse.value.KeyId));
    } else {
      return Failure(Types.ComAmazonawsKms(retResponse.error));
    }
  }
}
