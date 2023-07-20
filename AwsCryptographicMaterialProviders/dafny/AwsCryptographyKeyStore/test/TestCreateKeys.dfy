// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "Fixtures.dfy"
include "../src/Structure.dfy"
include "CleanupItems.dfy"

module TestCreateKeys {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers
  import opened Fixtures
  import Structure
  import UTF8
  import CleanupItems
  import DDBKeystoreOperations
  import UUID

  method {:test} TestCreateBranchAndBeaconKeys()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    var branchKeyId :- expect keyStore.CreateKey(Types.CreateKeyInput(
                                                   branchKeyIdentifier := None,
                                                   encryptionContext := None
                                                 ));

    var beaconKeyResult :- expect keyStore.GetBeaconKey(
      Types.GetBeaconKeyInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier
      ));

    var activeResult :- expect keyStore.GetActiveBranchKey(
      Types.GetActiveBranchKeyInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier
      ));

    var branchKeyVersion :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionResult :- expect keyStore.GetBranchKeyVersion(
      Types.GetBranchKeyVersionInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier,
        branchKeyVersion := branchKeyVersion
      ));

    // Since this process uses a read DDB table,
    // the number of records will forever increase.
    // To avoid this, remove the items.
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, branchKeyVersion, ddbClient);
    CleanupItems.DeleteActive(branchKeyId.branchKeyIdentifier, ddbClient);

    expect beaconKeyResult.beaconKeyMaterials.beaconKey.Some?;
    expect |beaconKeyResult.beaconKeyMaterials.beaconKey.value| == 32;
    expect |activeResult.branchKeyMaterials.branchKey| == 32;
    expect versionResult.branchKeyMaterials.branchKey == activeResult.branchKeyMaterials.branchKey;
    expect versionResult.branchKeyMaterials.branchKeyIdentifier
        == activeResult.branchKeyMaterials.branchKeyIdentifier
        == beaconKeyResult.beaconKeyMaterials.beaconKeyIdentifier;
    expect versionResult.branchKeyMaterials.branchKeyVersion == activeResult.branchKeyMaterials.branchKeyVersion;

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#createkey
    //= type=test
    //# If no branch key id is provided,
    //# then this operation MUST create a [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt)
    //# to be used as the branch key id.
    var idByteUUID :- expect UUID.ToByteArray(activeResult.branchKeyMaterials.branchKeyIdentifier);
    var idRoundTrip :- expect UUID.FromByteArray(idByteUUID);
    expect idRoundTrip == activeResult.branchKeyMaterials.branchKeyIdentifier;


    //= aws-encryption-sdk-specification/framework/branch-key-store.md#branch-key-and-beacon-key-creation
    //= type=test
    //# This guid MUST be [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt)
    var versionString :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionByteUUID :- expect UUID.ToByteArray(versionString);
    var versionRoundTrip :- expect UUID.FromByteArray(versionByteUUID);
    expect versionRoundTrip == versionString;

  }

  method {:test} TestCreateOptions()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    // Use a UUID so multiple tests can run :)
    var id :- expect UUID.GenerateUUID();

    var encryptionContext :- expect EncodeEncryptionContext(map[
                                                              "some" := "encryption",
                                                              "context" := "values"
                                                            ]);

    var branchKeyId :- expect keyStore.CreateKey(Types.CreateKeyInput(
                                                   branchKeyIdentifier := Some(id),
                                                   encryptionContext := Some(encryptionContext)
                                                 ));

    var beaconKeyResult :- expect keyStore.GetBeaconKey(
      Types.GetBeaconKeyInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier
      ));

    var activeResult :- expect keyStore.GetActiveBranchKey(
      Types.GetActiveBranchKeyInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier
      ));

    var branchKeyVersion :- expect UTF8.Decode(activeResult.branchKeyMaterials.branchKeyVersion);
    var versionResult :- expect keyStore.GetBranchKeyVersion(
      Types.GetBranchKeyVersionInput(
        branchKeyIdentifier := branchKeyId.branchKeyIdentifier,
        branchKeyVersion := branchKeyVersion
      ));

    // Since this process uses a read DDB table,
    // the number of records will forever increase.
    // To avoid this, remove the items.
    CleanupItems.DeleteVersion(branchKeyId.branchKeyIdentifier, branchKeyVersion, ddbClient);
    CleanupItems.DeleteActive(branchKeyId.branchKeyIdentifier, ddbClient);


    expect id
        == versionResult.branchKeyMaterials.branchKeyIdentifier
        == activeResult.branchKeyMaterials.branchKeyIdentifier
        == beaconKeyResult.beaconKeyMaterials.beaconKeyIdentifier;

    expect encryptionContext
        == versionResult.branchKeyMaterials.encryptionContext
        == activeResult.branchKeyMaterials.encryptionContext
        == beaconKeyResult.beaconKeyMaterials.encryptionContext;

  }

  method {:test} TestCreateDuplicate()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);

    var attempt := keyStore.CreateKey(Types.CreateKeyInput(
                                        branchKeyIdentifier := Some(branchKeyId),
                                        encryptionContext := None
                                      ));

    expect attempt.Failure?;
  }

  method {:test} InsertingADuplicateWillFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();

    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(
      branchKeyId,
      branchKeyIdActiveVersion,
      "",
      "",
      keyArn,
      map[]
    );

    var output := DDBKeystoreOperations.WriteNewKeyToStore(
      Structure.ToAttributeMap(encryptionContext, [1]),
      Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]),
      Structure.ToAttributeMap(Structure.BeaconKeyEncryptionContext(encryptionContext), [3]),
      branchKeyStoreName,
      ddbClient
    );

    expect output.Failure?;
  }

  method {:test} InsertingADuplicateWillWithADifferentVersionFail()
  {
    var ddbClient :- expect DDB.DynamoDBClient();

    var encryptionContext := Structure.DecryptOnlyBranchKeyEncryptionContext(
      branchKeyId,
      "!= branchKeyIdActiveVersion",
      "",
      "",
      keyArn,
      map[]
    );

    var output := DDBKeystoreOperations.WriteNewKeyToStore(
      Structure.ToAttributeMap(encryptionContext, [1]),
      Structure.ToAttributeMap(Structure.ActiveBranchKeyEncryptionContext(encryptionContext), [2]),
      Structure.ToAttributeMap(Structure.BeaconKeyEncryptionContext(encryptionContext), [3]),
      branchKeyStoreName,
      ddbClient
    );

    expect output.Failure?;
  }

  // See CreateKey operation for details
  method EncodeEncryptionContext(
    input: map<string,string>
  )
    returns (output: Result<Types.EncryptionContext, string>)
  {
    var encodedEncryptionContext
      := set k <- input
      ::
        (UTF8.Encode(k), UTF8.Encode(input[k]), k);
    :- Need(forall i <- encodedEncryptionContext
              ::
                && i.0.Success?
                && i.1.Success?
                && var encoded := UTF8.Decode(i.0.value);
                && encoded.Success?
                && i.2 == encoded.value
           ,
            "Unable to encode string");

    output := Success(map i <- encodedEncryptionContext :: i.0.value := i.1.value);
  }
}
