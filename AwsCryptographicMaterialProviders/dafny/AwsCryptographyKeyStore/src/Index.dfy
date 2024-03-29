// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/AwsCryptographyKeyStoreTypes.dfy"
include "AwsCryptographyKeyStoreOperations.dfy"
include "../../../dafny/AwsCryptographicMaterialProviders/src/AwsArnParsing.dfy"
include "../../AwsCryptographicMaterialProviders/src/Keyrings/AwsKms/AwsKmsUtils.dfy"

module {:extern "software.amazon.cryptography.keystore.internaldafny"}
  KeyStore refines AbstractAwsCryptographyKeyStoreService
{
  import opened AwsArnParsing
  import opened AwsKmsUtils
  import Operations = AwsCryptographyKeyStoreOperations
  import KMSOperations = Com.Amazonaws.Kms
  import DDBOperations =  Com.Amazonaws.Dynamodb
  import KMS = ComAmazonawsKmsTypes
  import DDB = ComAmazonawsDynamodbTypes
  import UUID

  // There is no sensible default, so define something that passes verification but will fail at runtime
  function method DefaultKeyStoreConfig(): KeyStoreConfig
  {
    KeyStoreConfig(
      ddbTableName := "None",
      kmsConfiguration := KMSConfiguration.kmsKeyArn("1234abcd-12ab-34cd-56ef-1234567890ab"),
      logicalKeyStoreName := "None",
      id := None,
      grantTokens := None,
      kmsClient := None,
      ddbClient := None
    )
  }

  method KeyStore(config: KeyStoreConfig)
    returns (res: Result<KeyStoreClient, Error>)
    ensures res.Success? ==>
              && res.value is KeyStoreClient
              && var rconfig := (res.value as KeyStoreClient).config;
              && KMS.IsValid_KeyIdType(rconfig.kmsConfiguration.kmsKeyArn)
              && DDB.IsValid_TableName(config.ddbTableName)
              && GetValidGrantTokens(config.grantTokens).Success?
              && (config.kmsClient.Some? ==> rconfig.kmsClient == config.kmsClient.value)
              && (config.ddbClient.Some? ==> rconfig.ddbClient == config.ddbClient.value
                                             && rconfig.kmsClient.ValidState()
                                             && rconfig.ddbClient.ValidState())
    ensures
      && !DDB.IsValid_TableName(config.ddbTableName)
      && !KMS.IsValid_KeyIdType(config.kmsConfiguration.kmsKeyArn)
      && ParseAwsKmsArn(config.kmsConfiguration.kmsKeyArn).Failure?
      ==>
        res.Failure?
  {
    :- Need(
      && KMS.IsValid_KeyIdType(config.kmsConfiguration.kmsKeyArn)
      && ParseAwsKmsArn(config.kmsConfiguration.kmsKeyArn).Success?,
      Types.KeyStoreException(
        message := "Invalid AWS KMS Key Arn")
    );

    //= aws-encryption-sdk-specification/framework/branch-key-store.md#initialization
    //# The following inputs MAY be specified to create a KeyStore:
    var grantTokens := GetValidGrantTokens(config.grantTokens);
    :- Need(
      && grantTokens.Success?,
      Types.KeyStoreException(
        message := "CreateKey received invalid grant tokens")
    );

    var keyStoreId;

    if config.id.Some? {
      keyStoreId := config.id.value;
    } else {
      //= aws-encryption-sdk-specification/framework/branch-key-store.md#keystore-id
      //# If one is not supplied, then a [version 4 UUID](https://www.ietf.org/rfc/rfc4122.txt) MUST be used.
      var maybeUuid := UUID.GenerateUUID();
      var uuid :- maybeUuid
      .MapFailure(e => Types.KeyStoreException(message := e));
      keyStoreId := uuid;
    }

    var kmsClient: KMS.IKMSClient;
    var ddbClient: DDB.IDynamoDBClient;

    var keyArn := ParseAwsKmsIdentifier(config.kmsConfiguration.kmsKeyArn);
    var kmsRegion := GetRegion(keyArn.value);

    if config.kmsClient.None? {
      var maybeKmsClient := KMSOperations.KMSClientForRegion(kmsRegion.value);
      kmsClient :- maybeKmsClient
      .MapFailure(e => Types.ComAmazonawsKms(ComAmazonawsKms := e));
    } else {
      kmsClient := config.kmsClient.value;
    }

    if config.ddbClient.None? {
      var maybeDdbClient := DDBOperations.DDBClientForRegion(kmsRegion.value);
      ddbClient :- maybeDdbClient
      .MapFailure(e => Types.ComAmazonawsDynamodb(ComAmazonawsDynamodb := e));
    } else {
      ddbClient := config.ddbClient.value;

      // This is true but to prove it requires changes to smithy-dafny.
      assume {:axiom} ddbClient.Modifies !! kmsClient.Modifies;
    }

      //= aws-encryption-sdk-specification/framework/branch-key-store.md#initialization
      //# The following inputs MUST be specified to create a KeyStore:
    :- Need(
      DDB.IsValid_TableName(config.ddbTableName),
      Types.KeyStoreException(
        message := "Invalid Amazon DynamoDB Table Name")
    );

    var client := new KeyStoreClient(
      Operations.Config(
      id := keyStoreId,
      ddbTableName := config.ddbTableName,
      logicalKeyStoreName := config.logicalKeyStoreName,
      kmsConfiguration := config.kmsConfiguration,
      grantTokens := grantTokens.value,
      kmsClient := kmsClient,
      ddbClient := ddbClient
      )
    );
    return Success(client);
  }

  class KeyStoreClient... {

    predicate {:vcs_split_on_every_assert} {:rlimit 3000} ValidState() {
      && Operations.ValidInternalConfig?(config)
      && History !in Operations.ModifiesInternalConfig(config)
      && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor(config: Operations.InternalConfig)
    {
      this.config := config;
      History := new IKeyStoreClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }
  }
}
