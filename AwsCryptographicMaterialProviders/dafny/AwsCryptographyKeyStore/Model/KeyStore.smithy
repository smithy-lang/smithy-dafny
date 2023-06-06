// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace aws.cryptography.keyStore

// The top level namespace for this project.
// Contains an entry-point for helper methods,
// and common structures used throughout this project.

use aws.polymorph#localService
use aws.polymorph#reference
use aws.polymorph#extendable
use aws.polymorph#dafnyUtf8Bytes
use aws.polymorph#javadoc

use com.amazonaws.dynamodb#TableName
use com.amazonaws.dynamodb#TableArn
use com.amazonaws.dynamodb#DynamoDB_20120810

use com.amazonaws.kms#TrentService


@dafnyUtf8Bytes
string Utf8Bytes

@reference(service: TrentService)
structure KmsClientReference {}

@reference(service: DynamoDB_20120810)
structure DdbClientReference {}

@localService(
  sdkId: "KeyStore",
  config: KeyStoreConfig,
  dependencies: [
    DynamoDB_20120810,
    TrentService
  ] 
)
service KeyStore {
  version: "2023-04-01",
  operations: [
    GetKeyStoreInfo,
    CreateKeyStore,
    CreateKey,
    VersionKey,
    GetActiveBranchKey,
    GetBranchKeyVersion,
    GetBeaconKey,
    BranchKeyStatusResolution
  ],
  errors: [KeyStoreException]
}

structure KeyStoreConfig {
  @required
  @javadoc("The DynamoDB table name that backs this Key Store.")
  ddbTableName: TableName,
  @required
  @javadoc("The AWS KMS Key that protects this Key Store.")
  kmsConfiguration: KMSConfiguration,
  @required
  @javadoc("The logical name for this Key Store, which is cryptographically bound to the keys it holds.")
  logicalKeyStoreName: String,
  
  @javadoc("An identifier for this Key Store.")
  id: String,
  @javadoc("The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.")
  grantTokens: GrantTokenList,
  @javadoc("The DynamoDB client this Key Store uses to call Amazon DynamoDB.")
  ddbClient: DdbClientReference,
  @javadoc("The KMS client this Key Store uses to call AWS KMS.")
  kmsClient: KmsClientReference,
}

union KMSConfiguration {
  kmsKeyArn: KmsKeyArn
}

@javadoc("Returns the configuration information for a Key Store.")
operation GetKeyStoreInfo {
  output: GetKeyStoreInfoOutput
}

@javadoc("The configuration information for a Key Store.")
structure GetKeyStoreInfoOutput {
  @required
  @javadoc("An identifier for this Key Store.")
  keyStoreId: String,
  @required
  @javadoc("The DynamoDB table name that backs this Key Store.")
  keyStoreName: TableName,
  @required
  @javadoc("The logical name for this Key Store, which is cryptographically bound to the keys it holds.")
  logicalKeyStoreName: String,
  @required
  @javadoc("The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.")
  grantTokens: GrantTokenList,
  @required
  @javadoc("The AWS KMS Key that protects this Key Store.")
  kmsConfiguration: KMSConfiguration
}

@javadoc("Create the DynamoDB table that backs this Key Store based on the Key Store configuration. If a table already exists, validate it is configured as expected.")
operation CreateKeyStore {
  input: CreateKeyStoreInput,
  output: CreateKeyStoreOutput
}

structure CreateKeyStoreInput {
}

@javadoc("Outputs for Key Store DynamoDB table creation.")
structure CreateKeyStoreOutput {
  @required
  @javadoc("The ARN of the DynamoDB table that backs this Key Store.")
  tableArn: com.amazonaws.dynamodb#TableArn
}

// CreateKey will create two keys to add to the key store
// One is the branch key, which is used in the hierarchical keyring
// The second is a beacon key that is used as a root key to
// derive different beacon keys per beacon.
@javadoc("Create a new Branch Key in the Key Store. Additionally create a Beacon Key that is tied to this Branch Key.")
operation CreateKey {
  output: CreateKeyOutput
}

@javadoc("Outputs for Branch Key creation.")
structure CreateKeyOutput {
  @required
  @javadoc("A identifier for the created Branch Key.")
  branchKeyIdentifier: String
}

// VersionKey will create a new branch key under the 
// provided branchKeyIdentifier and rotate the "older" material 
// on the key store under the branchKeyIdentifier. This operation MUST NOT
// rotate the beacon key under the branchKeyIdentifier.
@javadoc("Create a new ACTIVE version of an existing Branch Key in the Key Store, and set the previously ACTIVE version to DECRYPT_ONLY.")
operation VersionKey {
  input: VersionKeyInput
}

@javadoc("Inputs for versioning a Branch Key.")
structure VersionKeyInput {
  @required
  @javadoc("The identifier for the Branch Key to be versioned.")
  branchKeyIdentifier: String
}

@javadoc("Get the ACTIVE version for a particular Branch Key from the Key Store.")
operation GetActiveBranchKey {
  input: GetActiveBranchKeyInput,
  output: GetActiveBranchKeyOutput
}

@javadoc("Inputs for getting a Branch Key's ACTIVE version.")
structure GetActiveBranchKeyInput {
  @required
  @javadoc("The identifier for the Branch Key to get the ACTIVE version for.")
  branchKeyIdentifier: String
}

@javadoc("Outputs for getting a Branch Key's ACTIVE version.")
structure GetActiveBranchKeyOutput {
  @required
  @javadoc("The ACTIVE Branch Key version.")
  branchKeyVersion: Utf8Bytes,

  @required
  @javadoc("The key material for this ACTIVE Branch Key version.")
  branchKey: Secret
}

@javadoc("Get a particular version of a Branch Key from the Key Store.")
operation GetBranchKeyVersion {
  input: GetBranchKeyVersionInput,
  output: GetBranchKeyVersionOutput
}

@javadoc("Inputs for getting a version of a Branch Key.")
structure GetBranchKeyVersionInput {
  @required
  @javadoc("The identifier for the Branch Key to get a particular version for.")
  branchKeyIdentifier: String,

  @required
  @javadoc("The version to get.")
  branchKeyVersion: String
}

@javadoc("Outputs for getting a version of a Branch Key.")
structure GetBranchKeyVersionOutput {
  @required
  @javadoc("The version of this Branch Key.")
  branchKeyVersion: Utf8Bytes,

  @required
  @javadoc("The key material for this Branch Key version.")
  branchKey: Secret
}

@javadoc("Get a Beacon Key from the Key Store.")
operation GetBeaconKey {
  input: GetBeaconKeyInput,
  output: GetBeaconKeyOutput
}

@javadoc("Inputs for getting a Beacon Key")
structure GetBeaconKeyInput {
  @required
  @javadoc("The identifier of the Branch Key the Beacon Key is associated with.")
  branchKeyIdentifier: String
}

@javadoc("Outputs for getting a Beacon Key")
structure GetBeaconKeyOutput {
  @required
  @javadoc("The identifier for the Beacon Key.")
  beaconKeyIdentifier: String,

  @required
  @javadoc("The key material for this Beacon Key.")
  beaconKey: Secret,
}

@javadoc("In the case that the Key Store contains two ACTIVE Branch Key versions (this should not be possible in normal operation), attempt to resolve to one by making one ACTIVE version DECRYPT_ONLY.")
operation BranchKeyStatusResolution {
  input: BranchKeyStatusResolutionInput
}

@javadoc("Inputs for resolving a multiple ACTIVE versions state.")
structure BranchKeyStatusResolutionInput {
  @required
  @javadoc("The identifier for the Branch Key which has more than one ACTIVE version")
  branchKeyIdentifier: String
}

string KmsKeyArn

list GrantTokenList {
  member: String
}

@sensitive
blob Secret

///////////////////
// Errors

@error("client")
structure KeyStoreException {
  @required
  message: String,
}
