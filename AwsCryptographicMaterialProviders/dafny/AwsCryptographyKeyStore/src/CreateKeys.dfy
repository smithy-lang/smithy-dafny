// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "Structure.dfy"
include "DDBKeystoreOperations.dfy"
include "KMSKeystoreOperations.dfy"

module {:options "/functionSyntax:4" } CreateKeys {
  import opened StandardLibrary
  import opened Wrappers

  import Structure
  import KMSKeystoreOperations
  import DDBKeystoreOperations

  import opened Seq
  import opened UInt = StandardLibrary.UInt
  import Types = AwsCryptographyKeyStoreTypes
  import DDB = ComAmazonawsDynamodbTypes
  import KMS = ComAmazonawsKmsTypes


  //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
  //= type=implication
  //# To create a branch key, this operation MUST take the following:
  //#
  //# - `branchKeyId`: The identifier
  //# - `encryptionContext`: Additional encryption context to bind to the created keys
  method CreateBranchAndBeaconKeys(
    branchKeyIdentifier: string,
    customEncryptionContext: map<string, string>,
    timestamp: string,
    branchKeyVersion: string,
    ddbTableName: DDB.TableName,
    logicalKeyStoreName: string,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (output: Result<Types.CreateKeyOutput, Types.Error>)
    requires 0 < |branchKeyIdentifier|
    requires 0 < |branchKeyVersion|
    requires forall k <- customEncryptionContext :: DDB.IsValid_AttributeName(Structure.ENCRYPTION_CONTEXT_PREFIX + k)
    requires ddbClient.Modifies !! kmsClient.Modifies

    requires kmsClient.ValidState() && ddbClient.ValidState()
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //= type=implication
    //# This operation MUST create a [branch key](#branch-key) and a [beacon key](#beacon-key) according to
    //# the [Branch Key and Beacon Key Creation](#branch-key-and-beacon-key-creation) section.
    ensures output.Success?
            ==>

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# The operation MUST call [AWS KMS API GenerateDataKeyWithoutPlaintext](https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKeyWithoutPlaintext.html).

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# The call to AWS KMS GenerateDataKeyWithoutPlaintext MUST use the configured AWS KMS client to make the call.
              && |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 2

              && |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 1

              && var decryptOnlyEncryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(
                                                       branchKeyIdentifier,
                                                       branchKeyVersion,
                                                       timestamp,
                                                       logicalKeyStoreName,
                                                       kmsConfiguration.kmsKeyArn,
                                                       customEncryptionContext
                                                     );

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#logical-keystore-name
              //= type=implication
              //# The logical keystore name MUST be bound to every created key.
              && decryptOnlyEncryptionContext[Structure.TABLE_FIELD] == logicalKeyStoreName

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# The wrapped Branch Keys, DECRYPT_ONLY and ACTIVE, MUST be created according to [Wrapped Branch Key Creation](#wrapped-branch-key-creation).
              && WrappedBranchKeyCreation?(
                   Seq.Last(Seq.DropLast(kmsClient.History.GenerateDataKeyWithoutPlaintext)),
                   Seq.Last(kmsClient.History.ReEncrypt),
                   kmsClient,
                   kmsConfiguration,
                   grantTokens,
                   decryptOnlyEncryptionContext
                 )

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# The operation MUST call AWS KMS GenerateDataKeyWithoutPlaintext with a request constructed as follows:
              && var beaconKmsInput := Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).input;

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# - `KeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
              && beaconKmsInput.KeyId == kmsConfiguration.kmsKeyArn

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# - `NumberOfBytes` MUST be 32.
              && beaconKmsInput.NumberOfBytes == Some(32)

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# - `EncryptionContext` MUST be the [encryption context for beacon keys](#beacon-key-encryption-context).
              && beaconKmsInput.EncryptionContext == Some(Structure.BeaconKeyEncryptionContext(decryptOnlyEncryptionContext))

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
              //= type=implication
              //# - `GrantTokens` MUST be this keystore's [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
              && beaconKmsInput.GrantTokens == Some(grantTokens)

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
              //= type=implication
              //# If creation of the keys are successful,
              //# the operation MUST call Amazon DynamoDB TransactWriteItems according to the [write key material](#writing-branch-key-and-beacon-key-to-key-store) section.

              && Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.Success?
              && var beaconKmsOutput := Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.value;
              && beaconKmsOutput.CiphertextBlob.Some?

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#writing-branch-key-and-beacon-key-to-keystore
              //= type=implication
              //# To add the branch keys and a beacon key to the keystore the
              //# operation MUST call [Amazon DynamoDB API TransactWriteItems](https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_TransactWriteItems.html).

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#writing-branch-key-and-beacon-key-to-keystore
              //= type=implication
              //# The call to Amazon DynamoDB TransactWriteItems MUST use the configured Amazon DynamoDB Client to make the call.

              && |ddbClient.History.TransactWriteItems| == |old(ddbClient.History.TransactWriteItems)| + 1

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#writing-branch-key-and-beacon-key-to-keystore
              //= type=implication
              //# The operation MUST call Amazon DynamoDB TransactWriteItems with a request constructed as follows:
              && var writeNewKey := Seq.Last(ddbClient.History.TransactWriteItems).input;

              && 3 == |writeNewKey.TransactItems|

              && writeNewKey.TransactItems[0].Put.Some?
              && writeNewKey.TransactItems[0].Put.value.Item
                 == Structure.ToAttributeMap(
                      decryptOnlyEncryptionContext,
                      //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
                      //= type=implication
                      //# If the call to AWS KMS GenerateDataKeyWithoutPlaintext succeeds,
                      //# the operation MUST use the GenerateDataKeyWithoutPlaintext result `CiphertextBlob`
                      //# as the wrapped DECRYPT_ONLY Branch Key.
                      Seq.Last(Seq.DropLast(kmsClient.History.GenerateDataKeyWithoutPlaintext)).output.value.CiphertextBlob.value)

              && writeNewKey.TransactItems[1].Put.Some?
              && writeNewKey.TransactItems[1].Put.value.Item
                 == Structure.ToAttributeMap(
                      Structure.ActiveBranchKeyEncryptionContext(decryptOnlyEncryptionContext),
                      //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
                      //= type=implication
                      //# If the call to AWS KMS ReEncrypt succeeds,
                      //# the operation MUST use the ReEncrypt result `CiphertextBlob`
                      //# as the wrapped ACTIVE Branch Key.
                      Seq.Last(kmsClient.History.ReEncrypt).output.value.CiphertextBlob.value)

              && writeNewKey.TransactItems[2].Put.Some?
              && writeNewKey.TransactItems[2].Put.value.Item
                 == Structure.ToAttributeMap(
                      Structure.BeaconKeyEncryptionContext(decryptOnlyEncryptionContext),
                      //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
                      //= type=implication
                      //# If the call to AWS KMS GenerateDataKeyWithoutPlaintext succeeds,
                      //# the operation MUST use the `CiphertextBlob` as the wrapped Beacon Key.
                      beaconKmsOutput.CiphertextBlob.value)

              && Seq.Last(ddbClient.History.TransactWriteItems).output.Success?

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
              //= type=implication
              //# If writing to the keystore succeeds,
              //# the operation MUST return the branch-key-id that maps to both
              //# the branch key and the beacon key.
              && output.value.branchKeyIdentifier == branchKeyIdentifier


    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //= type=implication
    //# Otherwise, this operation MUST yield an error.
    ensures

      || (&& |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 1
          && Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.Failure?
          ==> output.Failure?)

      || (&& |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 1
          && Seq.Last(kmsClient.History.ReEncrypt).output.Failure?
          ==> output.Failure?)

      || (&& |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 2
          && Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.Failure?
          ==> output.Failure?)

      || (&& |ddbClient.History.TransactWriteItems| == |old(ddbClient.History.TransactWriteItems)| + 1
          && Seq.Last(ddbClient.History.TransactWriteItems).output.Failure?
          ==> output.Failure?)

  {

    var decryptOnlyEncryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(
      branchKeyIdentifier,
      branchKeyVersion,
      timestamp,
      logicalKeyStoreName,
      kmsConfiguration.kmsKeyArn,
      customEncryptionContext
    );
    var activeEncryptionContext := Structure.ActiveBranchKeyEncryptionContext(decryptOnlyEncryptionContext);
    var beaconEncryptionContext := Structure.BeaconKeyEncryptionContext(decryptOnlyEncryptionContext);

    var wrappedDecryptOnlyBranchKey :- KMSKeystoreOperations.GenerateKey(
      decryptOnlyEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );
    var wrappedActiveBranchKey :- KMSKeystoreOperations.ReEncryptKey(
      wrappedDecryptOnlyBranchKey.CiphertextBlob.value,
      decryptOnlyEncryptionContext,
      activeEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );
    var wrappedBeaconKey :- KMSKeystoreOperations.GenerateKey(
      beaconEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );


    var decryptOnlyBranchKeyItem := Structure.ToAttributeMap(
      decryptOnlyEncryptionContext,
      wrappedDecryptOnlyBranchKey.CiphertextBlob.value
    );
    var activeBranchKeyItem := Structure.ToAttributeMap(
      activeEncryptionContext,
      wrappedActiveBranchKey.CiphertextBlob.value
    );
    var beaconKeyItem := Structure.ToAttributeMap(
      beaconEncryptionContext,
      wrappedBeaconKey.CiphertextBlob.value
    );

    var _ :- DDBKeystoreOperations.WriteNewKeyToStore(
      decryptOnlyBranchKeyItem,
      activeBranchKeyItem,
      beaconKeyItem,
      ddbTableName,
      ddbClient
    );

    output := Success(
      Types.CreateKeyOutput(
        branchKeyIdentifier := branchKeyIdentifier
      ));
  }

  method VersionActiveBranchKey(
    input: Types.VersionKeyInput,
    timestamp: string,
    branchKeyVersion: string,
    ddbTableName: DDB.TableName,
    logicalKeyStoreName: string,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    kmsClient: KMS.IKMSClient,
    ddbClient: DDB.IDynamoDBClient
  )
    returns (output: Result<Types.VersionKeyOutput, Types.Error>)
    requires 0 < |input.branchKeyIdentifier| && 0 < |branchKeyVersion|
    requires ddbClient.Modifies !! kmsClient.Modifies

    requires kmsClient.ValidState() && ddbClient.ValidState()
    modifies ddbClient.Modifies, kmsClient.Modifies
    ensures ddbClient.ValidState() && kmsClient.ValidState()

    ensures output.Success?
            ==>
              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# VersionKey MUST first get the active version for the branch key from the keystore
              //# by calling AWS DDB `GetItem`
              //# using the `branch-key-id` as the Partition Key and `"branch:ACTIVE"` value as the Sort Key.
              && |ddbClient.History.GetItem| == |old(ddbClient.History.GetItem)| + 1
              && Seq.Last(ddbClient.History.GetItem).input.Key
                 == map[
                      Structure.BRANCH_KEY_IDENTIFIER_FIELD := DDB.AttributeValue.S(input.branchKeyIdentifier),
                      Structure.TYPE_FIELD := DDB.AttributeValue.S(Structure.BRANCH_KEY_ACTIVE_TYPE)
                    ]

              && Seq.Last(ddbClient.History.GetItem).output.Success?
              && Seq.Last(ddbClient.History.GetItem).output.value.Item.Some?
              && var oldActiveItem := Seq.Last(ddbClient.History.GetItem).output.value.Item.value;
              && Structure.BranchKeyItem?(oldActiveItem)
              && Structure.BRANCH_KEY_ACTIVE_VERSION_FIELD in oldActiveItem

              && KMSKeystoreOperations.AttemptKmsOperation?(kmsConfiguration, Structure.ToBranchKeyContext(oldActiveItem, logicalKeyStoreName))

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# The values on the AWS DDB response item
              //# MUST be authenticated according to [authenticating a keystore item](#authenticating-a-keystore-item).

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# The operation MUST use the configured `KMS SDK Client` to authenticate the value of the keystore item.
              && |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 2 // This 2 because we need to wrap the new version

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# The operation MUST call [AWS KMS API ReEncrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_ReEncrypt.html)
              //# with a request constructed as follows:
              && var reEncryptInput := Seq.Last(Seq.DropLast(kmsClient.History.ReEncrypt)).input;

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `SourceEncryptionContext` MUST be the [encryption context](#encryption-context) constructed above
              && reEncryptInput.SourceEncryptionContext == Some(Structure.ToBranchKeyContext(oldActiveItem, logicalKeyStoreName))

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `SourceKeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
              && reEncryptInput.SourceKeyId == Some(kmsConfiguration.kmsKeyArn)

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `CiphertextBlob` MUST be the `enc` attribute value on the AWS DDB response item
              && reEncryptInput.CiphertextBlob == oldActiveItem[Structure.BRANCH_KEY_FIELD].B

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `GrantTokens` MUST be the configured [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
              && reEncryptInput.GrantTokens == Some(grantTokens)

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `DestinationKeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
              && reEncryptInput.DestinationKeyId == kmsConfiguration.kmsKeyArn

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#authenticating-a-keystore-item
              //= type=implication
              //# - `DestinationEncryptionContext` MUST be the [encryption context](#encryption-context) constructed above
              && reEncryptInput.DestinationEncryptionContext == Some(Structure.ToBranchKeyContext(oldActiveItem, logicalKeyStoreName))

              && |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 1

              && var decryptOnlyEncryptionContext := Structure.NewVersionFromActiveBranchKeyEncryptionContext(
                                                       Structure.ToBranchKeyContext(oldActiveItem, logicalKeyStoreName),
                                                       branchKeyVersion,
                                                       timestamp
                                                     );

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# The wrapped Branch Keys, DECRYPT_ONLY and ACTIVE, MUST be created according to [Wrapped Branch Key Creation](#wrapped-branch-key-creation).
              && WrappedBranchKeyCreation?(
                   Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext),
                   Seq.Last(kmsClient.History.ReEncrypt),
                   kmsClient,
                   kmsConfiguration,
                   grantTokens,
                   decryptOnlyEncryptionContext
                 )

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# The call to Amazon DynamoDB TransactWriteItems MUST use the configured Amazon DynamoDB Client to make the call.

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# To add the new branch key to the keystore,
              //# the operation MUST call [Amazon DynamoDB API TransactWriteItems](https://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_TransactWriteItems.html).
              && |ddbClient.History.TransactWriteItems| == |old(ddbClient.History.TransactWriteItems)| + 1

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# The operation MUST call Amazon DynamoDB TransactWriteItems with a request constructed as follows:
              && var writeNewKey := Seq.Last(ddbClient.History.TransactWriteItems).input;

              && 2 == |writeNewKey.TransactItems|

              && writeNewKey.TransactItems[0].Put.Some?
              && writeNewKey.TransactItems[0].Put.value.Item
                 == Structure.ToAttributeMap(
                      decryptOnlyEncryptionContext,
                      //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
                      //= type=implication
                      //# If the call to AWS KMS GenerateDataKeyWithoutPlaintext succeeds,
                      //# the operation MUST use the GenerateDataKeyWithoutPlaintext result `CiphertextBlob`
                      //# as the wrapped DECRYPT_ONLY Branch Key.
                      Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.value.CiphertextBlob.value)

              && writeNewKey.TransactItems[1].Put.Some?
              && writeNewKey.TransactItems[1].Put.value.Item
                 == Structure.ToAttributeMap(
                      Structure.ActiveBranchKeyEncryptionContext(decryptOnlyEncryptionContext),
                      //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
                      //= type=implication
                      //# If the call to AWS KMS ReEncrypt succeeds,
                      //# the operation MUST use the ReEncrypt result `CiphertextBlob`
                      //# as the wrapped ACTIVE Branch Key.
                      Seq.Last(kmsClient.History.ReEncrypt).output.value.CiphertextBlob.value)

              && Seq.Last(ddbClient.History.TransactWriteItems).output.Success?

              //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
              //= type=implication
              //# If DDB TransactWriteItems is successful, this operation MUST return a successful response containing no additional data.
              && output == Success(Types.VersionKeyOutput)

    ensures
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# If the item fails to authenticate this operation MUST fail.
      || (&& |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 1
          && Seq.Last(kmsClient.History.ReEncrypt).output.Failure?
          ==> output.Failure?)

      //= aws-encryption-sdk-specification/framework/branch-key-store.md#versionkey
      //= type=implication
      //# Otherwise, this operation MUST yield an error.

      || (&& |kmsClient.History.GenerateDataKeyWithoutPlaintext| == |old(kmsClient.History.GenerateDataKeyWithoutPlaintext)| + 1
          && Seq.Last(kmsClient.History.GenerateDataKeyWithoutPlaintext).output.Failure?
          ==> output.Failure?)

      || (&& |kmsClient.History.ReEncrypt| == |old(kmsClient.History.ReEncrypt)| + 2
          && Seq.Last(kmsClient.History.ReEncrypt).output.Failure?
          ==> output.Failure?)

      || (&& |ddbClient.History.TransactWriteItems| == |old(ddbClient.History.TransactWriteItems)| + 1
          && Seq.Last(ddbClient.History.TransactWriteItems).output.Failure?
          ==> output.Failure?)

  {

    var oldActiveItem :- DDBKeystoreOperations.GetActiveBranchKeyItem(
      input.branchKeyIdentifier,
      ddbTableName,
      ddbClient
    );

    var oldActiveEncryptionContext := Structure.ToBranchKeyContext(oldActiveItem, logicalKeyStoreName);

    :- Need(
      && KMSKeystoreOperations.AttemptKmsOperation?(kmsConfiguration, oldActiveEncryptionContext),
      Types.KeyStoreException(
        message := "Wrapping AWS KMS key in dynamodb does not match configured AWS KMS information."));

    var _ :- KMSKeystoreOperations.ReEncryptKey(
      oldActiveItem[Structure.BRANCH_KEY_FIELD].B,
      oldActiveEncryptionContext,
      oldActiveEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );

    var decryptOnlyEncryptionContext := Structure.NewVersionFromActiveBranchKeyEncryptionContext(
      oldActiveEncryptionContext,
      branchKeyVersion,
      timestamp
    );

    var activeEncryptionContext := Structure.ActiveBranchKeyEncryptionContext(decryptOnlyEncryptionContext);

    var wrappedDecryptOnlyBranchKey :- KMSKeystoreOperations.GenerateKey(
      decryptOnlyEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );
    var wrappedActiveBranchKey :- KMSKeystoreOperations.ReEncryptKey(
      wrappedDecryptOnlyBranchKey.CiphertextBlob.value,
      decryptOnlyEncryptionContext,
      activeEncryptionContext,
      kmsConfiguration,
      grantTokens,
      kmsClient
    );

    var decryptOnlyBranchKeyItem: Structure.VersionBranchKeyItem := Structure.ToAttributeMap(
      decryptOnlyEncryptionContext,
      wrappedDecryptOnlyBranchKey.CiphertextBlob.value
    );
    var activeBranchKeyItem: Structure.ActiveBranchKeyItem := Structure.ToAttributeMap(
      activeEncryptionContext,
      wrappedActiveBranchKey.CiphertextBlob.value
    );

    var _ :- DDBKeystoreOperations.WriteNewBranchKeyVersionToKeystore(
      decryptOnlyBranchKeyItem,
      activeBranchKeyItem,
      ddbTableName,
      ddbClient
    );

    assert && |ddbClient.History.TransactWriteItems| == |old(ddbClient.History.TransactWriteItems)| + 1;

    output := Success(Types.VersionKeyOutput());
  }


  ghost predicate WrappedBranchKeyCreation?(
    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# The operation MUST call [AWS KMS API GenerateDataKeyWithoutPlaintext](https://docs.aws.amazon.com/kms/latest/APIReference/API_GenerateDataKeyWithoutPlaintext.html).
    generateHistory: KMS.DafnyCallEvent<KMS.GenerateDataKeyWithoutPlaintextRequest, Result<KMS.GenerateDataKeyWithoutPlaintextResponse, KMS.Error>>,
    reEncryptHistory: KMS.DafnyCallEvent<KMS.ReEncryptRequest, Result<KMS.ReEncryptResponse, KMS.Error>>,
    kmsClient: KMS.IKMSClient,
    kmsConfiguration: Types.KMSConfiguration,
    grantTokens: KMS.GrantTokenList,
    decryptOnlyEncryptionContext: map<string, string>
  )
    reads kmsClient.History
    requires Structure.BranchKeyContext?(decryptOnlyEncryptionContext)
    requires Structure.BRANCH_KEY_TYPE_PREFIX < decryptOnlyEncryptionContext[Structure.TYPE_FIELD]

    // Ideally this be in "the things I added"
    // But I don't know how to express that yet.

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# The call to AWS KMS GenerateDataKeyWithoutPlaintext MUST use the configured AWS KMS client to make the call.
    requires generateHistory in kmsClient.History.GenerateDataKeyWithoutPlaintext
    requires reEncryptHistory in kmsClient.History.ReEncrypt
  {

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# The operation MUST call AWS KMS GenerateDataKeyWithoutPlaintext with a request constructed as follows:
    && var decryptOnlyKmsInput := generateHistory.input;

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `KeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
    && decryptOnlyKmsInput.KeyId == kmsConfiguration.kmsKeyArn

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `NumberOfBytes` MUST be 32.
    && decryptOnlyKmsInput.NumberOfBytes == Some(32)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `EncryptionContext` MUST be the [DECRYPT_ONLY encryption context for branch keys](#decrypt_only-encryption-context).
    && decryptOnlyKmsInput.EncryptionContext == Some(decryptOnlyEncryptionContext)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - GenerateDataKeyWithoutPlaintext `GrantTokens` MUST be this keystore's [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
    && decryptOnlyKmsInput.GrantTokens == Some(grantTokens)

    && generateHistory.output.Success?
    && generateHistory.output.value.CiphertextBlob.Some?

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# The operation MUST call [AWS KMS API ReEncrypt](https://docs.aws.amazon.com/kms/latest/APIReference/API_ReEncrypt.html)
    //# with a request constructed as follows:
    && var activeInput := reEncryptHistory.input;

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `SourceKeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
    && activeInput.SourceKeyId == Some(kmsConfiguration.kmsKeyArn)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `DestinationKeyId` MUST be the configured `AWS KMS Key ARN` in the [AWS KMS Configuration](#aws-kms-configuration) for this keystore
    && activeInput.DestinationKeyId == kmsConfiguration.kmsKeyArn

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - ReEncrypt `GrantTokens` MUST be this keystore's [grant tokens](https://docs.aws.amazon.com/kms/latest/developerguide/concepts.html#grant_token).
    && activeInput.GrantTokens == Some(grantTokens)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `CiphertextBlob` MUST be the wrapped DECRYPT_ONLY Branch Key.
    && activeInput.CiphertextBlob == generateHistory.output.value.CiphertextBlob.value

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `SourceEncryptionContext` MUST be the [DECRYPT_ONLY encryption context for branch keys](#decrypt_only-encryption-context).
    && activeInput.SourceEncryptionContext == Some(decryptOnlyEncryptionContext)

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#wrapped-branch-key-creation
    //= type=implication
    //# - `DestinationEncryptionContext` MUST be the [ACTIVE encryption context for branch keys](#active-encryption-context).
    && activeInput.DestinationEncryptionContext == Some(Structure.ActiveBranchKeyEncryptionContext(decryptOnlyEncryptionContext))

    && reEncryptHistory.output.Success?
    && reEncryptHistory.output.value.CiphertextBlob.Some?

  }

}
