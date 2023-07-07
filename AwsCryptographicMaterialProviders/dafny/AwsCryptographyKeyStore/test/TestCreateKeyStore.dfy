// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "../../AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"

module TestCreateKeyStore {
  import Types = AwsCryptographyKeyStoreTypes
  import KMS = Com.Amazonaws.Kms
  import DDB = Com.Amazonaws.Dynamodb
  import KeyStore
  import opened Wrappers
  import opened AwsArnParsing

  const keyStoreName := "KeyStoreTestTable";
  const logicalKeyStoreName := keyStoreName;

  // THESE ARE TESTING RESOURCES DO NOT USE IN A PRODUCTION ENVIRONMENT
  const keyArn := "arn:aws:kms:us-west-2:370957321024:key/9d989aa2-2f9c-438c-a745-cc57d3ad0126";

  method {:test} TestCreateKeyStore()
  {
    var kmsClient :- expect KMS.KMSClient();
    var ddbClient :- expect DDB.DynamoDBClient();
    var kmsConfig := Types.KMSConfiguration.kmsKeyArn(keyArn);

    var keyStoreConfig := Types.KeyStoreConfig(
      id := None,
      kmsConfiguration := kmsConfig,
      logicalKeyStoreName := logicalKeyStoreName,
      grantTokens := None,
      ddbTableName := keyStoreName,
      ddbClient := Some(ddbClient),
      kmsClient := Some(kmsClient)
    );

    var keyStore :- expect KeyStore.KeyStore(keyStoreConfig);
    // we are not actually creating a table in CI but testing we have configured a table
    // with the expected construction
    var keyStoreArn :- expect keyStore.CreateKeyStore(Types.CreateKeyStoreInput());

    expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).Success?;
    expect AwsArnParsing.ParseAmazonDynamodbTableName(keyStoreArn.tableArn).value == keyStoreName;
  }
}
