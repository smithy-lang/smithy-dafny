// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "Fixtures.dfy"

module TestConfig {
  import Types = AwsCryptographyKeyStoreTypes
  import ComAmazonawsKmsTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers
  import opened Fixtures
  import UUID

  method {:test} TestInvalidKmsKeyArnConfig() {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyId);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Failure?;
    expect keyStore.error == Types.KeyStoreException(message := "Invalid AWS KMS Key Arn");
  }

  method {:test} TestValidConfig() {
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

    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;

    var conf :- expect keyStore.value.GetKeyStoreInfo();

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#keystore-id
    //= type=test
    //# If one is not supplied, then a [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt) MUST be used.
    var idByteUUID :- expect UUID.ToByteArray(conf.keyStoreId);
    var idRoundTrip :- expect UUID.FromByteArray(idByteUUID);
    expect idRoundTrip == conf.keyStoreId;

    expect conf.keyStoreName == branchKeyStoreName;
    expect conf.logicalKeyStoreName == logicalKeyStoreName;
    expect conf.kmsConfiguration == kmsConfig;

  }

  method {:test} TestValidConfigNoClients() {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);

    // Test with no kms client supplied
    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := None
    );
    var keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;

    // Test with no ddb client supplied
    keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := None,
      kmsClient := Some(kmsClient)
    );
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;

    // Test with no clients supplied
    keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := branchKeyStoreName,
      ddbClient := None,
      kmsClient := None
    );
    keyStore := KeyStore.KeyStore(keyStoreConfig);
    expect keyStore.Success?;
  }
}
