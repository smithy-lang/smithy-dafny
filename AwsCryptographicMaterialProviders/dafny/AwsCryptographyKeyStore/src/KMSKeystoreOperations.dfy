// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "Structure.dfy"

module {:options "/functionSyntax:4" } KMSKeystoreOperations {
  import opened Wrappers
  import opened UInt = StandardLibrary.UInt
  import Seq
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes
  import UTF8
  import Structure


  predicate AttemptKmsOperation?(kmsConfiguration: Types.KMSConfiguration, encryptionContext: Structure.BranchKeyContext)
  {
    match kmsConfiguration
    case kmsKeyArn(arn) => arn == encryptionContext[Structure.KMS_FIELD]
  }

  method GenerateKey(
    encryptionContext: Structure.BranchKeyContext,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient
  )
    returns (res: Result<KMS.GenerateDataKeyWithoutPlaintextResponse, Types.Error>)
    requires AttemptKmsOperation?(kmsConfiguration, encryptionContext)
    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()
    ensures
      && |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 1
      && KMS.GenerateDataKeyWithoutPlaintextRequest(
           KeyId := kmsConfiguration.kmsKeyArn,
           EncryptionContext := Some(encryptionContext),
           KeySpec := None,
           NumberOfBytes := Some(32),
           GrantTokens := Some(grantTokens)
         )
         == Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).input
      && old(kmsClient.History.GenerateDataKeyWithoutPlaintext) < kmsClient.History.GenerateDataKeyWithoutPlaintext
      && old(kmsClient.History.ReEncrypt) == kmsClient.History.ReEncrypt

    ensures res.Success? ==>
              && res.value.KeyId.Some?
              && res.value.CiphertextBlob.Some?
              && KMS.IsValid_CiphertextType(res.value.CiphertextBlob.value)
              && var kmsOperationOutput := Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output;
              && kmsOperationOutput.Success?
              && kmsOperationOutput.value == res.value
  {
    var generatorRequest := KMS.GenerateDataKeyWithoutPlaintextRequest(
      KeyId := kmsConfiguration.kmsKeyArn,
      EncryptionContext := Some(encryptionContext),
      KeySpec := None,
      NumberOfBytes := Some(32),
      GrantTokens := Some(grantTokens)
    );

    var maybeGenerateResponse := kmsClient.GenerateDataKeyWithoutPlaintext(generatorRequest);
    var generateResponse :- maybeGenerateResponse
    .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

    :- Need(
      && generateResponse.KeyId.Some?,
      Types.KeyStoreException(
        message := "Invalid response from KMS GenerateDataKey:: Invalid Key Id")
    );

    :- Need(
      && generateResponse.CiphertextBlob.Some?
      && KMS.IsValid_CiphertextType(generateResponse.CiphertextBlob.value),
      Types.KeyStoreException(
        message := "Invalid response from AWS KMS GenerateDataKey: Invalid ciphertext")
    );

    return Success(generateResponse);
  }

  method ReEncryptKey(
    ciphertext: seq<uint8>,
    sourceEncryptionContext: Structure.BranchKeyContext,
    destinationEncryptionContext: Structure.BranchKeyContext,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient
  )
    returns (res: Result<KMS.ReEncryptResponse, Types.Error>)
    requires KMS.IsValid_CiphertextType(ciphertext)
    requires
      // This is to validate the encryption context
      || (destinationEncryptionContext == sourceEncryptionContext)
      || (
           && Structure.BRANCH_KEY_TYPE_PREFIX < sourceEncryptionContext[Structure.TYPE_FIELD]
           && Structure.BRANCH_KEY_ACTIVE_VERSION_FIELD !in sourceEncryptionContext
           && destinationEncryptionContext == Structure.ActiveBranchKeyEncryptionContext(sourceEncryptionContext)
         )
    requires AttemptKmsOperation?(kmsConfiguration, destinationEncryptionContext)
    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()

    ensures
      && |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 1
      && KMS.ReEncryptRequest(
           CiphertextBlob := ciphertext,
           SourceEncryptionContext := Some(sourceEncryptionContext),
           SourceKeyId := Some(kmsConfiguration.kmsKeyArn),
           DestinationKeyId := kmsConfiguration.kmsKeyArn,
           DestinationEncryptionContext := Some(destinationEncryptionContext),
           SourceEncryptionAlgorithm := None,
           DestinationEncryptionAlgorithm := None,
           GrantTokens := Some(grantTokens)
         )
         == Seq.Last(kmsClient.History.ReEncrypt).input
      && old(kmsClient.History.ReEncrypt) < kmsClient.History.ReEncrypt
      && old(kmsClient.History.GenerateDataKeyWithoutPlaintext) == kmsClient.History.GenerateDataKeyWithoutPlaintext

    ensures res.Success? ==>
              && res.value.CiphertextBlob.Some?
              && res.value.SourceKeyId.Some?
              && res.value.KeyId.Some?
              && res.value.SourceKeyId.value == kmsConfiguration.kmsKeyArn
              && res.value.KeyId.value == kmsConfiguration.kmsKeyArn
              && KMS.IsValid_CiphertextType(res.value.CiphertextBlob.value)
              && var kmsOperationOutput := Seq.Last(kmsClient.History.ReEncrypt).output;
              && kmsOperationOutput.Success?
              && kmsOperationOutput.value == res.value
  {
    var reEncryptRequest := KMS.ReEncryptRequest(
      CiphertextBlob := ciphertext,
      SourceEncryptionContext := Some(sourceEncryptionContext),
      SourceKeyId := Some(kmsConfiguration.kmsKeyArn),
      DestinationKeyId := kmsConfiguration.kmsKeyArn,
      DestinationEncryptionContext := Some(destinationEncryptionContext),
      SourceEncryptionAlgorithm := None,
      DestinationEncryptionAlgorithm := None,
      GrantTokens := Some(grantTokens)
    );

    var maybeReEncryptResponse := kmsClient.ReEncrypt(reEncryptRequest);
    var reEncryptResponse :- maybeReEncryptResponse
    .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));

    :- Need(
      && reEncryptResponse.SourceKeyId.Some?
      && reEncryptResponse.KeyId.Some?
      && reEncryptResponse.SourceKeyId.value == kmsConfiguration.kmsKeyArn
      && reEncryptResponse.KeyId.value == kmsConfiguration.kmsKeyArn,
      Types.KeyStoreException(
        message := "Invalid response from KMS GenerateDataKey:: Invalid Key Id")
    );

    :- Need(
      && reEncryptResponse.CiphertextBlob.Some?
      && KMS.IsValid_CiphertextType(reEncryptResponse.CiphertextBlob.value),
      Types.KeyStoreException(
        message := "Invalid response from AWS KMS ReEncrypt: Invalid ciphertext.")
    );

    return Success(reEncryptResponse);
  }

  method DecryptKey(
    encryptionContext: Structure.BranchKeyContext,
    item: Structure.BranchKeyItem,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient
  )
    returns (output: Result<KMS.DecryptResponse, Types.Error>)
    requires AttemptKmsOperation?(kmsConfiguration, encryptionContext)
    requires item == Structure.ToAttributeMap(encryptionContext, item[Structure.BRANCH_KEY_FIELD].B)

    requires kmsClient.ValidState()
    modifies kmsClient.Modifies
    ensures kmsClient.ValidState()

    ensures
      && |kmsClient.History.Decrypt| == |old(kmsClient.History.Decrypt)| + 1
      && KMS.DecryptRequest(
           CiphertextBlob := item[Structure.BRANCH_KEY_FIELD].B,
           EncryptionContext := Some(encryptionContext),
           GrantTokens := Some(grantTokens),
           KeyId := Some(kmsConfiguration.kmsKeyArn),
           EncryptionAlgorithm := None
         )
         == Seq.Last(kmsClient.History.Decrypt).input;
    ensures output.Success?
            ==>
              && Seq.Last(kmsClient.History.Decrypt).output.Success?
              && output.value == Seq.Last(kmsClient.History.Decrypt).output.value
              && output.value.Plaintext.Some?
              && 32 == |output.value.Plaintext.value|
  {

    var maybeDecryptResponse := kmsClient.Decrypt(
      KMS.DecryptRequest(
        CiphertextBlob := item[Structure.BRANCH_KEY_FIELD].B,
        EncryptionContext := Some(encryptionContext),
        GrantTokens := Some(grantTokens),
        KeyId := Some(kmsConfiguration.kmsKeyArn),
        EncryptionAlgorithm := None
      )
    );
    var decryptResponse :- maybeDecryptResponse.MapFailure(e => Types.ComAmazonawsKms(e));

    :- Need(
      && decryptResponse.Plaintext.Some?
      && 32 == |decryptResponse.Plaintext.value|,
      Types.KeyStoreException(
        message := "Invalid response from AWS KMS Decrypt: Key is not 32 bytes.")
    );

    output := Success(decryptResponse);

  }

}
