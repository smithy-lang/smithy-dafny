// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../StandardLibrary/src/Index.dfy"
module {:extern "software.amazon.cryptography.services.kms.internaldafny.types" } ComAmazonawsKmsTypes
{
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
    // Generic helpers for verification of mock/unit tests.
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  // Begin Generated Types

  datatype AlgorithmSpec =
    | RSAES_PKCS1_V1_5
    | RSAES_OAEP_SHA_1
    | RSAES_OAEP_SHA_256
  type AliasList = seq<AliasListEntry>
  datatype AliasListEntry = | AliasListEntry (
    nameonly AliasName: Option<AliasNameType> := Option.None ,
    nameonly AliasArn: Option<ArnType> := Option.None ,
    nameonly TargetKeyId: Option<KeyIdType> := Option.None ,
    nameonly CreationDate: Option<string> := Option.None ,
    nameonly LastUpdatedDate: Option<string> := Option.None
  )
  type AliasNameType = x: string | IsValid_AliasNameType(x) witness *
  predicate method IsValid_AliasNameType(x: string) {
    ( 1 <= |x| <= 256 )
  }
  type ArnType = x: string | IsValid_ArnType(x) witness *
  predicate method IsValid_ArnType(x: string) {
    ( 20 <= |x| <= 2048 )
  }
  type AWSAccountIdType = string
  type BooleanType = bool
  datatype CancelKeyDeletionRequest = | CancelKeyDeletionRequest (
    nameonly KeyId: KeyIdType
  )
  datatype CancelKeyDeletionResponse = | CancelKeyDeletionResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None
  )
  type CiphertextType = x: seq<uint8> | IsValid_CiphertextType(x) witness *
  predicate method IsValid_CiphertextType(x: seq<uint8>) {
    ( 1 <= |x| <= 6144 )
  }
  type CloudHsmClusterIdType = x: string | IsValid_CloudHsmClusterIdType(x) witness *
  predicate method IsValid_CloudHsmClusterIdType(x: string) {
    ( 19 <= |x| <= 24 )
  }
  datatype ConnectCustomKeyStoreRequest = | ConnectCustomKeyStoreRequest (
    nameonly CustomKeyStoreId: CustomKeyStoreIdType
  )
  datatype ConnectCustomKeyStoreResponse = | ConnectCustomKeyStoreResponse (

                                           )
  datatype ConnectionErrorCodeType =
    | INVALID_CREDENTIALS
    | CLUSTER_NOT_FOUND
    | NETWORK_ERRORS
    | INTERNAL_ERROR
    | INSUFFICIENT_CLOUDHSM_HSMS
    | USER_LOCKED_OUT
    | USER_NOT_FOUND
    | USER_LOGGED_IN
    | SUBNET_NOT_FOUND
  datatype ConnectionStateType =
    | CONNECTED
    | CONNECTING
    | FAILED
    | DISCONNECTED
    | DISCONNECTING
  datatype CreateAliasRequest = | CreateAliasRequest (
    nameonly AliasName: AliasNameType ,
    nameonly TargetKeyId: KeyIdType
  )
  datatype CreateCustomKeyStoreRequest = | CreateCustomKeyStoreRequest (
    nameonly CustomKeyStoreName: CustomKeyStoreNameType ,
    nameonly CloudHsmClusterId: CloudHsmClusterIdType ,
    nameonly TrustAnchorCertificate: TrustAnchorCertificateType ,
    nameonly KeyStorePassword: KeyStorePasswordType
  )
  datatype CreateCustomKeyStoreResponse = | CreateCustomKeyStoreResponse (
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None
  )
  datatype CreateGrantRequest = | CreateGrantRequest (
    nameonly KeyId: KeyIdType ,
    nameonly GranteePrincipal: PrincipalIdType ,
    nameonly RetiringPrincipal: Option<PrincipalIdType> := Option.None ,
    nameonly Operations: GrantOperationList ,
    nameonly Constraints: Option<GrantConstraints> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly Name: Option<GrantNameType> := Option.None
  )
  datatype CreateGrantResponse = | CreateGrantResponse (
    nameonly GrantToken: Option<GrantTokenType> := Option.None ,
    nameonly GrantId: Option<GrantIdType> := Option.None
  )
  datatype CreateKeyRequest = | CreateKeyRequest (
    nameonly Policy: Option<PolicyType> := Option.None ,
    nameonly Description: Option<DescriptionType> := Option.None ,
    nameonly KeyUsage: Option<KeyUsageType> := Option.None ,
    nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> := Option.None ,
    nameonly KeySpec: Option<KeySpec> := Option.None ,
    nameonly Origin: Option<OriginType> := Option.None ,
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None ,
    nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> := Option.None ,
    nameonly Tags: Option<TagList> := Option.None ,
    nameonly MultiRegion: Option<NullableBooleanType> := Option.None
  )
  datatype CreateKeyResponse = | CreateKeyResponse (
    nameonly KeyMetadata: Option<KeyMetadata> := Option.None
  )
  datatype CustomerMasterKeySpec =
    | RSA_2048
    | RSA_3072
    | RSA_4096
    | ECC_NIST_P256
    | ECC_NIST_P384
    | ECC_NIST_P521
    | ECC_SECG_P256K1
    | SYMMETRIC_DEFAULT
  type CustomKeyStoreIdType = x: string | IsValid_CustomKeyStoreIdType(x) witness *
  predicate method IsValid_CustomKeyStoreIdType(x: string) {
    ( 1 <= |x| <= 64 )
  }
  type CustomKeyStoreNameType = x: string | IsValid_CustomKeyStoreNameType(x) witness *
  predicate method IsValid_CustomKeyStoreNameType(x: string) {
    ( 1 <= |x| <= 256 )
  }
  type CustomKeyStoresList = seq<CustomKeyStoresListEntry>
  datatype CustomKeyStoresListEntry = | CustomKeyStoresListEntry (
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None ,
    nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> := Option.None ,
    nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> := Option.None ,
    nameonly TrustAnchorCertificate: Option<TrustAnchorCertificateType> := Option.None ,
    nameonly ConnectionState: Option<ConnectionStateType> := Option.None ,
    nameonly ConnectionErrorCode: Option<ConnectionErrorCodeType> := Option.None ,
    nameonly CreationDate: Option<string> := Option.None
  )
  datatype DataKeyPairSpec =
    | RSA_2048
    | RSA_3072
    | RSA_4096
    | ECC_NIST_P256
    | ECC_NIST_P384
    | ECC_NIST_P521
    | ECC_SECG_P256K1
  datatype DataKeySpec =
    | AES_256
    | AES_128
  datatype DecryptRequest = | DecryptRequest (
    nameonly CiphertextBlob: CiphertextType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  datatype DecryptResponse = | DecryptResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly Plaintext: Option<PlaintextType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  datatype DeleteAliasRequest = | DeleteAliasRequest (
    nameonly AliasName: AliasNameType
  )
  datatype DeleteCustomKeyStoreRequest = | DeleteCustomKeyStoreRequest (
    nameonly CustomKeyStoreId: CustomKeyStoreIdType
  )
  datatype DeleteCustomKeyStoreResponse = | DeleteCustomKeyStoreResponse (

                                          )
  datatype DeleteImportedKeyMaterialRequest = | DeleteImportedKeyMaterialRequest (
    nameonly KeyId: KeyIdType
  )
  datatype DescribeCustomKeyStoresRequest = | DescribeCustomKeyStoresRequest (
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None ,
    nameonly CustomKeyStoreName: Option<CustomKeyStoreNameType> := Option.None ,
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None
  )
  datatype DescribeCustomKeyStoresResponse = | DescribeCustomKeyStoresResponse (
    nameonly CustomKeyStores: Option<CustomKeyStoresList> := Option.None ,
    nameonly NextMarker: Option<MarkerType> := Option.None ,
    nameonly Truncated: Option<BooleanType> := Option.None
  )
  datatype DescribeKeyRequest = | DescribeKeyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype DescribeKeyResponse = | DescribeKeyResponse (
    nameonly KeyMetadata: Option<KeyMetadata> := Option.None
  )
  type DescriptionType = x: string | IsValid_DescriptionType(x) witness *
  predicate method IsValid_DescriptionType(x: string) {
    ( 0 <= |x| <= 8192 )
  }
  datatype DisableKeyRequest = | DisableKeyRequest (
    nameonly KeyId: KeyIdType
  )
  datatype DisableKeyRotationRequest = | DisableKeyRotationRequest (
    nameonly KeyId: KeyIdType
  )
  datatype DisconnectCustomKeyStoreRequest = | DisconnectCustomKeyStoreRequest (
    nameonly CustomKeyStoreId: CustomKeyStoreIdType
  )
  datatype DisconnectCustomKeyStoreResponse = | DisconnectCustomKeyStoreResponse (

                                              )
  datatype EnableKeyRequest = | EnableKeyRequest (
    nameonly KeyId: KeyIdType
  )
  datatype EnableKeyRotationRequest = | EnableKeyRotationRequest (
    nameonly KeyId: KeyIdType
  )
  datatype EncryptionAlgorithmSpec =
    | SYMMETRIC_DEFAULT
    | RSAES_OAEP_SHA_1
    | RSAES_OAEP_SHA_256
  type EncryptionAlgorithmSpecList = seq<EncryptionAlgorithmSpec>
  type EncryptionContextKey = string
  type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>
  type EncryptionContextValue = string
  datatype EncryptRequest = | EncryptRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Plaintext: PlaintextType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  datatype EncryptResponse = | EncryptResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  type ErrorMessageType = string
  datatype ExpirationModelType =
    | KEY_MATERIAL_EXPIRES
    | KEY_MATERIAL_DOES_NOT_EXPIRE
  datatype GenerateDataKeyPairRequest = | GenerateDataKeyPairRequest (
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly KeyId: KeyIdType ,
    nameonly KeyPairSpec: DataKeyPairSpec ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype GenerateDataKeyPairResponse = | GenerateDataKeyPairResponse (
    nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly PrivateKeyPlaintext: Option<PlaintextType> := Option.None ,
    nameonly PublicKey: Option<PublicKeyType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly KeyPairSpec: Option<DataKeyPairSpec> := Option.None
  )
  datatype GenerateDataKeyPairWithoutPlaintextRequest = | GenerateDataKeyPairWithoutPlaintextRequest (
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly KeyId: KeyIdType ,
    nameonly KeyPairSpec: DataKeyPairSpec ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype GenerateDataKeyPairWithoutPlaintextResponse = | GenerateDataKeyPairWithoutPlaintextResponse (
    nameonly PrivateKeyCiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly PublicKey: Option<PublicKeyType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly KeyPairSpec: Option<DataKeyPairSpec> := Option.None
  )
  datatype GenerateDataKeyRequest = | GenerateDataKeyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly NumberOfBytes: Option<NumberOfBytesType> := Option.None ,
    nameonly KeySpec: Option<DataKeySpec> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype GenerateDataKeyResponse = | GenerateDataKeyResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly Plaintext: Option<PlaintextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None
  )
  datatype GenerateDataKeyWithoutPlaintextRequest = | GenerateDataKeyWithoutPlaintextRequest (
    nameonly KeyId: KeyIdType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly KeySpec: Option<DataKeySpec> := Option.None ,
    nameonly NumberOfBytes: Option<NumberOfBytesType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype GenerateDataKeyWithoutPlaintextResponse = | GenerateDataKeyWithoutPlaintextResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None
  )
  datatype GenerateRandomRequest = | GenerateRandomRequest (
    nameonly NumberOfBytes: Option<NumberOfBytesType> := Option.None ,
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None
  )
  datatype GenerateRandomResponse = | GenerateRandomResponse (
    nameonly Plaintext: Option<PlaintextType> := Option.None
  )
  datatype GetKeyPolicyRequest = | GetKeyPolicyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly PolicyName: PolicyNameType
  )
  datatype GetKeyPolicyResponse = | GetKeyPolicyResponse (
    nameonly Policy: Option<PolicyType> := Option.None
  )
  datatype GetKeyRotationStatusRequest = | GetKeyRotationStatusRequest (
    nameonly KeyId: KeyIdType
  )
  datatype GetKeyRotationStatusResponse = | GetKeyRotationStatusResponse (
    nameonly KeyRotationEnabled: Option<BooleanType> := Option.None
  )
  datatype GetParametersForImportRequest = | GetParametersForImportRequest (
    nameonly KeyId: KeyIdType ,
    nameonly WrappingAlgorithm: AlgorithmSpec ,
    nameonly WrappingKeySpec: WrappingKeySpec
  )
  datatype GetParametersForImportResponse = | GetParametersForImportResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly ImportToken: Option<CiphertextType> := Option.None ,
    nameonly PublicKey: Option<PlaintextType> := Option.None ,
    nameonly ParametersValidTo: Option<string> := Option.None
  )
  datatype GetPublicKeyRequest = | GetPublicKeyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype GetPublicKeyResponse = | GetPublicKeyResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly PublicKey: Option<PublicKeyType> := Option.None ,
    nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> := Option.None ,
    nameonly KeySpec: Option<KeySpec> := Option.None ,
    nameonly KeyUsage: Option<KeyUsageType> := Option.None ,
    nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> := Option.None ,
    nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> := Option.None
  )
  datatype GrantConstraints = | GrantConstraints (
    nameonly EncryptionContextSubset: Option<EncryptionContextType> := Option.None ,
    nameonly EncryptionContextEquals: Option<EncryptionContextType> := Option.None
  )
  type GrantIdType = x: string | IsValid_GrantIdType(x) witness *
  predicate method IsValid_GrantIdType(x: string) {
    ( 1 <= |x| <= 128 )
  }
  type GrantList = seq<GrantListEntry>
  datatype GrantListEntry = | GrantListEntry (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly GrantId: Option<GrantIdType> := Option.None ,
    nameonly Name: Option<GrantNameType> := Option.None ,
    nameonly CreationDate: Option<string> := Option.None ,
    nameonly GranteePrincipal: Option<PrincipalIdType> := Option.None ,
    nameonly RetiringPrincipal: Option<PrincipalIdType> := Option.None ,
    nameonly IssuingAccount: Option<PrincipalIdType> := Option.None ,
    nameonly Operations: Option<GrantOperationList> := Option.None ,
    nameonly Constraints: Option<GrantConstraints> := Option.None
  )
  type GrantNameType = x: string | IsValid_GrantNameType(x) witness *
  predicate method IsValid_GrantNameType(x: string) {
    ( 1 <= |x| <= 256 )
  }
  datatype GrantOperation =
    | Decrypt
    | Encrypt
    | GenerateDataKey
    | GenerateDataKeyWithoutPlaintext
    | ReEncryptFrom
    | ReEncryptTo
    | Sign
    | Verify
    | GetPublicKey
    | CreateGrant
    | RetireGrant
    | DescribeKey
    | GenerateDataKeyPair
    | GenerateDataKeyPairWithoutPlaintext
  type GrantOperationList = seq<GrantOperation>
  type GrantTokenList = x: seq<GrantTokenType> | IsValid_GrantTokenList(x) witness *
  predicate method IsValid_GrantTokenList(x: seq<GrantTokenType>) {
    ( 0 <= |x| <= 10 )
  }
  type GrantTokenType = x: string | IsValid_GrantTokenType(x) witness *
  predicate method IsValid_GrantTokenType(x: string) {
    ( 1 <= |x| <= 8192 )
  }
  datatype ImportKeyMaterialRequest = | ImportKeyMaterialRequest (
    nameonly KeyId: KeyIdType ,
    nameonly ImportToken: CiphertextType ,
    nameonly EncryptedKeyMaterial: CiphertextType ,
    nameonly ValidTo: Option<string> := Option.None ,
    nameonly ExpirationModel: Option<ExpirationModelType> := Option.None
  )
  datatype ImportKeyMaterialResponse = | ImportKeyMaterialResponse (

                                       )
  type KeyIdType = x: string | IsValid_KeyIdType(x) witness *
  predicate method IsValid_KeyIdType(x: string) {
    ( 1 <= |x| <= 2048 )
  }
  type KeyList = seq<KeyListEntry>
  datatype KeyListEntry = | KeyListEntry (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly KeyArn: Option<ArnType> := Option.None
  )
  datatype KeyManagerType =
    | AWS
    | CUSTOMER
  datatype KeyMetadata = | KeyMetadata (
    nameonly AWSAccountId: Option<AWSAccountIdType> := Option.None ,
    nameonly KeyId: KeyIdType ,
    nameonly Arn: Option<ArnType> := Option.None ,
    nameonly CreationDate: Option<string> := Option.None ,
    nameonly Enabled: Option<BooleanType> := Option.None ,
    nameonly Description: Option<DescriptionType> := Option.None ,
    nameonly KeyUsage: Option<KeyUsageType> := Option.None ,
    nameonly KeyState: Option<KeyState> := Option.None ,
    nameonly DeletionDate: Option<string> := Option.None ,
    nameonly ValidTo: Option<string> := Option.None ,
    nameonly Origin: Option<OriginType> := Option.None ,
    nameonly CustomKeyStoreId: Option<CustomKeyStoreIdType> := Option.None ,
    nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> := Option.None ,
    nameonly ExpirationModel: Option<ExpirationModelType> := Option.None ,
    nameonly KeyManager: Option<KeyManagerType> := Option.None ,
    nameonly CustomerMasterKeySpec: Option<CustomerMasterKeySpec> := Option.None ,
    nameonly KeySpec: Option<KeySpec> := Option.None ,
    nameonly EncryptionAlgorithms: Option<EncryptionAlgorithmSpecList> := Option.None ,
    nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> := Option.None ,
    nameonly MultiRegion: Option<NullableBooleanType> := Option.None ,
    nameonly MultiRegionConfiguration: Option<MultiRegionConfiguration> := Option.None ,
    nameonly PendingDeletionWindowInDays: Option<PendingWindowInDaysType> := Option.None
  )
  datatype KeySpec =
    | RSA_2048
    | RSA_3072
    | RSA_4096
    | ECC_NIST_P256
    | ECC_NIST_P384
    | ECC_NIST_P521
    | ECC_SECG_P256K1
    | SYMMETRIC_DEFAULT
  datatype KeyState =
    | Creating
    | Enabled
    | Disabled
    | PendingDeletion
    | PendingImport
    | PendingReplicaDeletion
    | Unavailable
    | Updating
  type KeyStorePasswordType = x: string | IsValid_KeyStorePasswordType(x) witness *
  predicate method IsValid_KeyStorePasswordType(x: string) {
    ( 7 <= |x| <= 32 )
  }
  datatype KeyUsageType =
    | SIGN_VERIFY
    | ENCRYPT_DECRYPT
  type LimitType = x: int32 | IsValid_LimitType(x) witness *
  predicate method IsValid_LimitType(x: int32) {
    ( 1 <= x <= 1000 )
  }
  datatype ListAliasesRequest = | ListAliasesRequest (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None
  )
  datatype ListAliasesResponse = | ListAliasesResponse (
    nameonly Aliases: Option<AliasList> := Option.None ,
    nameonly NextMarker: Option<MarkerType> := Option.None ,
    nameonly Truncated: Option<BooleanType> := Option.None
  )
  datatype ListGrantsRequest = | ListGrantsRequest (
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None ,
    nameonly KeyId: KeyIdType ,
    nameonly GrantId: Option<GrantIdType> := Option.None ,
    nameonly GranteePrincipal: Option<PrincipalIdType> := Option.None
  )
  datatype ListGrantsResponse = | ListGrantsResponse (
    nameonly Grants: Option<GrantList> := Option.None ,
    nameonly NextMarker: Option<MarkerType> := Option.None ,
    nameonly Truncated: Option<BooleanType> := Option.None
  )
  datatype ListKeyPoliciesRequest = | ListKeyPoliciesRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None
  )
  datatype ListKeyPoliciesResponse = | ListKeyPoliciesResponse (
    nameonly PolicyNames: Option<PolicyNameList> := Option.None ,
    nameonly NextMarker: Option<MarkerType> := Option.None ,
    nameonly Truncated: Option<BooleanType> := Option.None
  )
  datatype ListKeysRequest = | ListKeysRequest (
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None
  )
  datatype ListResourceTagsRequest = | ListResourceTagsRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None
  )
  datatype ListResourceTagsResponse = | ListResourceTagsResponse (
    nameonly Tags: Option<TagList> := Option.None ,
    nameonly NextMarker: Option<MarkerType> := Option.None ,
    nameonly Truncated: Option<BooleanType> := Option.None
  )
  datatype ListRetirableGrantsRequest = | ListRetirableGrantsRequest (
    nameonly Limit: Option<LimitType> := Option.None ,
    nameonly Marker: Option<MarkerType> := Option.None ,
    nameonly RetiringPrincipal: PrincipalIdType
  )
  type MarkerType = x: string | IsValid_MarkerType(x) witness *
  predicate method IsValid_MarkerType(x: string) {
    ( 1 <= |x| <= 1024 )
  }
  datatype MessageType =
    | RAW
    | DIGEST
  datatype MultiRegionConfiguration = | MultiRegionConfiguration (
    nameonly MultiRegionKeyType: Option<MultiRegionKeyType> := Option.None ,
    nameonly PrimaryKey: Option<MultiRegionKey> := Option.None ,
    nameonly ReplicaKeys: Option<MultiRegionKeyList> := Option.None
  )
  datatype MultiRegionKey = | MultiRegionKey (
    nameonly Arn: Option<ArnType> := Option.None ,
    nameonly Region: Option<RegionType> := Option.None
  )
  type MultiRegionKeyList = seq<MultiRegionKey>
  datatype MultiRegionKeyType =
    | PRIMARY
    | REPLICA
  type NullableBooleanType = bool
  type NumberOfBytesType = x: int32 | IsValid_NumberOfBytesType(x) witness *
  predicate method IsValid_NumberOfBytesType(x: int32) {
    ( 1 <= x <= 1024 )
  }
  datatype OriginType =
    | AWS_KMS
    | EXTERNAL
    | AWS_CLOUDHSM
  type PendingWindowInDaysType = x: int32 | IsValid_PendingWindowInDaysType(x) witness *
  predicate method IsValid_PendingWindowInDaysType(x: int32) {
    ( 1 <= x <= 365 )
  }
  type PlaintextType = x: seq<uint8> | IsValid_PlaintextType(x) witness *
  predicate method IsValid_PlaintextType(x: seq<uint8>) {
    ( 1 <= |x| <= 4096 )
  }
  type PolicyNameList = seq<PolicyNameType>
  type PolicyNameType = x: string | IsValid_PolicyNameType(x) witness *
  predicate method IsValid_PolicyNameType(x: string) {
    ( 1 <= |x| <= 128 )
  }
  type PolicyType = x: string | IsValid_PolicyType(x) witness *
  predicate method IsValid_PolicyType(x: string) {
    ( 1 <= |x| <= 131072 )
  }
  type PrincipalIdType = x: string | IsValid_PrincipalIdType(x) witness *
  predicate method IsValid_PrincipalIdType(x: string) {
    ( 1 <= |x| <= 256 )
  }
  type PublicKeyType = x: seq<uint8> | IsValid_PublicKeyType(x) witness *
  predicate method IsValid_PublicKeyType(x: seq<uint8>) {
    ( 1 <= |x| <= 8192 )
  }
  datatype PutKeyPolicyRequest = | PutKeyPolicyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly PolicyName: PolicyNameType ,
    nameonly Policy: PolicyType ,
    nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> := Option.None
  )
  datatype ReEncryptRequest = | ReEncryptRequest (
    nameonly CiphertextBlob: CiphertextType ,
    nameonly SourceEncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly SourceKeyId: Option<KeyIdType> := Option.None ,
    nameonly DestinationKeyId: KeyIdType ,
    nameonly DestinationEncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype ReEncryptResponse = | ReEncryptResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly SourceKeyId: Option<KeyIdType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  type RegionType = x: string | IsValid_RegionType(x) witness *
  predicate method IsValid_RegionType(x: string) {
    ( 1 <= |x| <= 32 )
  }
  datatype ReplicateKeyRequest = | ReplicateKeyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly ReplicaRegion: RegionType ,
    nameonly Policy: Option<PolicyType> := Option.None ,
    nameonly BypassPolicyLockoutSafetyCheck: Option<BooleanType> := Option.None ,
    nameonly Description: Option<DescriptionType> := Option.None ,
    nameonly Tags: Option<TagList> := Option.None
  )
  datatype ReplicateKeyResponse = | ReplicateKeyResponse (
    nameonly ReplicaKeyMetadata: Option<KeyMetadata> := Option.None ,
    nameonly ReplicaPolicy: Option<PolicyType> := Option.None ,
    nameonly ReplicaTags: Option<TagList> := Option.None
  )
  datatype RetireGrantRequest = | RetireGrantRequest (
    nameonly GrantToken: Option<GrantTokenType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly GrantId: Option<GrantIdType> := Option.None
  )
  datatype RevokeGrantRequest = | RevokeGrantRequest (
    nameonly KeyId: KeyIdType ,
    nameonly GrantId: GrantIdType
  )
  datatype ScheduleKeyDeletionRequest = | ScheduleKeyDeletionRequest (
    nameonly KeyId: KeyIdType ,
    nameonly PendingWindowInDays: Option<PendingWindowInDaysType> := Option.None
  )
  datatype ScheduleKeyDeletionResponse = | ScheduleKeyDeletionResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly DeletionDate: Option<string> := Option.None ,
    nameonly KeyState: Option<KeyState> := Option.None ,
    nameonly PendingWindowInDays: Option<PendingWindowInDaysType> := Option.None
  )
  datatype SigningAlgorithmSpec =
    | RSASSA_PSS_SHA_256
    | RSASSA_PSS_SHA_384
    | RSASSA_PSS_SHA_512
    | RSASSA_PKCS1_V1_5_SHA_256
    | RSASSA_PKCS1_V1_5_SHA_384
    | RSASSA_PKCS1_V1_5_SHA_512
    | ECDSA_SHA_256
    | ECDSA_SHA_384
    | ECDSA_SHA_512
  type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>
  datatype SignRequest = | SignRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Message: PlaintextType ,
    nameonly MessageType: Option<MessageType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly SigningAlgorithm: SigningAlgorithmSpec
  )
  datatype SignResponse = | SignResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly Signature: Option<CiphertextType> := Option.None ,
    nameonly SigningAlgorithm: Option<SigningAlgorithmSpec> := Option.None
  )
  datatype Tag = | Tag (
    nameonly TagKey: TagKeyType ,
    nameonly TagValue: TagValueType
  )
  type TagKeyList = seq<TagKeyType>
  type TagKeyType = x: string | IsValid_TagKeyType(x) witness *
  predicate method IsValid_TagKeyType(x: string) {
    ( 1 <= |x| <= 128 )
  }
  type TagList = seq<Tag>
  datatype TagResourceRequest = | TagResourceRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Tags: TagList
  )
  type TagValueType = x: string | IsValid_TagValueType(x) witness *
  predicate method IsValid_TagValueType(x: string) {
    ( 0 <= |x| <= 256 )
  }
  class IKMSClientCallHistory {
    ghost constructor() {
      CancelKeyDeletion := [];
      ConnectCustomKeyStore := [];
      CreateAlias := [];
      CreateCustomKeyStore := [];
      CreateGrant := [];
      CreateKey := [];
      Decrypt := [];
      DeleteAlias := [];
      DeleteCustomKeyStore := [];
      DeleteImportedKeyMaterial := [];
      DescribeCustomKeyStores := [];
      DescribeKey := [];
      DisableKey := [];
      DisableKeyRotation := [];
      DisconnectCustomKeyStore := [];
      EnableKey := [];
      EnableKeyRotation := [];
      Encrypt := [];
      GenerateDataKey := [];
      GenerateDataKeyPair := [];
      GenerateDataKeyPairWithoutPlaintext := [];
      GenerateDataKeyWithoutPlaintext := [];
      GenerateRandom := [];
      GetKeyPolicy := [];
      GetKeyRotationStatus := [];
      GetParametersForImport := [];
      GetPublicKey := [];
      ImportKeyMaterial := [];
      ListAliases := [];
      ListGrants := [];
      ListKeyPolicies := [];
      ListResourceTags := [];
      PutKeyPolicy := [];
      ReEncrypt := [];
      ReplicateKey := [];
      RetireGrant := [];
      RevokeGrant := [];
      ScheduleKeyDeletion := [];
      Sign := [];
      TagResource := [];
      UntagResource := [];
      UpdateAlias := [];
      UpdateCustomKeyStore := [];
      UpdateKeyDescription := [];
      UpdatePrimaryRegion := [];
      Verify := [];
    }
    ghost var CancelKeyDeletion: seq<DafnyCallEvent<CancelKeyDeletionRequest, Result<CancelKeyDeletionResponse, Error>>>
    ghost var ConnectCustomKeyStore: seq<DafnyCallEvent<ConnectCustomKeyStoreRequest, Result<ConnectCustomKeyStoreResponse, Error>>>
    ghost var CreateAlias: seq<DafnyCallEvent<CreateAliasRequest, Result<(), Error>>>
    ghost var CreateCustomKeyStore: seq<DafnyCallEvent<CreateCustomKeyStoreRequest, Result<CreateCustomKeyStoreResponse, Error>>>
    ghost var CreateGrant: seq<DafnyCallEvent<CreateGrantRequest, Result<CreateGrantResponse, Error>>>
    ghost var CreateKey: seq<DafnyCallEvent<CreateKeyRequest, Result<CreateKeyResponse, Error>>>
    ghost var Decrypt: seq<DafnyCallEvent<DecryptRequest, Result<DecryptResponse, Error>>>
    ghost var DeleteAlias: seq<DafnyCallEvent<DeleteAliasRequest, Result<(), Error>>>
    ghost var DeleteCustomKeyStore: seq<DafnyCallEvent<DeleteCustomKeyStoreRequest, Result<DeleteCustomKeyStoreResponse, Error>>>
    ghost var DeleteImportedKeyMaterial: seq<DafnyCallEvent<DeleteImportedKeyMaterialRequest, Result<(), Error>>>
    ghost var DescribeCustomKeyStores: seq<DafnyCallEvent<DescribeCustomKeyStoresRequest, Result<DescribeCustomKeyStoresResponse, Error>>>
    ghost var DescribeKey: seq<DafnyCallEvent<DescribeKeyRequest, Result<DescribeKeyResponse, Error>>>
    ghost var DisableKey: seq<DafnyCallEvent<DisableKeyRequest, Result<(), Error>>>
    ghost var DisableKeyRotation: seq<DafnyCallEvent<DisableKeyRotationRequest, Result<(), Error>>>
    ghost var DisconnectCustomKeyStore: seq<DafnyCallEvent<DisconnectCustomKeyStoreRequest, Result<DisconnectCustomKeyStoreResponse, Error>>>
    ghost var EnableKey: seq<DafnyCallEvent<EnableKeyRequest, Result<(), Error>>>
    ghost var EnableKeyRotation: seq<DafnyCallEvent<EnableKeyRotationRequest, Result<(), Error>>>
    ghost var Encrypt: seq<DafnyCallEvent<EncryptRequest, Result<EncryptResponse, Error>>>
    ghost var GenerateDataKey: seq<DafnyCallEvent<GenerateDataKeyRequest, Result<GenerateDataKeyResponse, Error>>>
    ghost var GenerateDataKeyPair: seq<DafnyCallEvent<GenerateDataKeyPairRequest, Result<GenerateDataKeyPairResponse, Error>>>
    ghost var GenerateDataKeyPairWithoutPlaintext: seq<DafnyCallEvent<GenerateDataKeyPairWithoutPlaintextRequest, Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>>>
    ghost var GenerateDataKeyWithoutPlaintext: seq<DafnyCallEvent<GenerateDataKeyWithoutPlaintextRequest, Result<GenerateDataKeyWithoutPlaintextResponse, Error>>>
    ghost var GenerateRandom: seq<DafnyCallEvent<GenerateRandomRequest, Result<GenerateRandomResponse, Error>>>
    ghost var GetKeyPolicy: seq<DafnyCallEvent<GetKeyPolicyRequest, Result<GetKeyPolicyResponse, Error>>>
    ghost var GetKeyRotationStatus: seq<DafnyCallEvent<GetKeyRotationStatusRequest, Result<GetKeyRotationStatusResponse, Error>>>
    ghost var GetParametersForImport: seq<DafnyCallEvent<GetParametersForImportRequest, Result<GetParametersForImportResponse, Error>>>
    ghost var GetPublicKey: seq<DafnyCallEvent<GetPublicKeyRequest, Result<GetPublicKeyResponse, Error>>>
    ghost var ImportKeyMaterial: seq<DafnyCallEvent<ImportKeyMaterialRequest, Result<ImportKeyMaterialResponse, Error>>>
    ghost var ListAliases: seq<DafnyCallEvent<ListAliasesRequest, Result<ListAliasesResponse, Error>>>
    ghost var ListGrants: seq<DafnyCallEvent<ListGrantsRequest, Result<ListGrantsResponse, Error>>>
    ghost var ListKeyPolicies: seq<DafnyCallEvent<ListKeyPoliciesRequest, Result<ListKeyPoliciesResponse, Error>>>
    ghost var ListResourceTags: seq<DafnyCallEvent<ListResourceTagsRequest, Result<ListResourceTagsResponse, Error>>>
    ghost var PutKeyPolicy: seq<DafnyCallEvent<PutKeyPolicyRequest, Result<(), Error>>>
    ghost var ReEncrypt: seq<DafnyCallEvent<ReEncryptRequest, Result<ReEncryptResponse, Error>>>
    ghost var ReplicateKey: seq<DafnyCallEvent<ReplicateKeyRequest, Result<ReplicateKeyResponse, Error>>>
    ghost var RetireGrant: seq<DafnyCallEvent<RetireGrantRequest, Result<(), Error>>>
    ghost var RevokeGrant: seq<DafnyCallEvent<RevokeGrantRequest, Result<(), Error>>>
    ghost var ScheduleKeyDeletion: seq<DafnyCallEvent<ScheduleKeyDeletionRequest, Result<ScheduleKeyDeletionResponse, Error>>>
    ghost var Sign: seq<DafnyCallEvent<SignRequest, Result<SignResponse, Error>>>
    ghost var TagResource: seq<DafnyCallEvent<TagResourceRequest, Result<(), Error>>>
    ghost var UntagResource: seq<DafnyCallEvent<UntagResourceRequest, Result<(), Error>>>
    ghost var UpdateAlias: seq<DafnyCallEvent<UpdateAliasRequest, Result<(), Error>>>
    ghost var UpdateCustomKeyStore: seq<DafnyCallEvent<UpdateCustomKeyStoreRequest, Result<UpdateCustomKeyStoreResponse, Error>>>
    ghost var UpdateKeyDescription: seq<DafnyCallEvent<UpdateKeyDescriptionRequest, Result<(), Error>>>
    ghost var UpdatePrimaryRegion: seq<DafnyCallEvent<UpdatePrimaryRegionRequest, Result<(), Error>>>
    ghost var Verify: seq<DafnyCallEvent<VerifyRequest, Result<VerifyResponse, Error>>>
  }
  trait {:termination false} IKMSClient
  {
    // Helper to define any additional modifies/reads clauses.
    // If your operations need to mutate state,
    // add it in your constructor function:
    // Modifies := {your, fields, here, History};
    // If you do not need to mutate anything:
    // Modifies := {History};

    ghost const Modifies: set<object>
    // For an unassigned field defined in a trait,
    // Dafny can only assign a value in the constructor.
    // This means that for Dafny to reason about this value,
    // it needs some way to know (an invariant),
    // about the state of the object.
    // This builds on the Valid/Repr paradigm
    // To make this kind requires safe to add
    // to methods called from unverified code,
    // the predicate MUST NOT take any arguments.
    // This means that the correctness of this requires
    // MUST only be evaluated by the class itself.
    // If you require any additional mutation,
    // then you MUST ensure everything you need in ValidState.
    // You MUST also ensure ValidState in your constructor.
    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    ghost const History: IKMSClientCallHistory
    predicate CancelKeyDeletionEnsuresPublicly(input: CancelKeyDeletionRequest , output: Result<CancelKeyDeletionResponse, Error>)
    // The public method to be called by library consumers
    method CancelKeyDeletion ( input: CancelKeyDeletionRequest )
      returns (output: Result<CancelKeyDeletionResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CancelKeyDeletion
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CancelKeyDeletionEnsuresPublicly(input, output)
      ensures History.CancelKeyDeletion == old(History.CancelKeyDeletion) + [DafnyCallEvent(input, output)]

    predicate ConnectCustomKeyStoreEnsuresPublicly(input: ConnectCustomKeyStoreRequest , output: Result<ConnectCustomKeyStoreResponse, Error>)
    // The public method to be called by library consumers
    method ConnectCustomKeyStore ( input: ConnectCustomKeyStoreRequest )
      returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ConnectCustomKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ConnectCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.ConnectCustomKeyStore == old(History.ConnectCustomKeyStore) + [DafnyCallEvent(input, output)]

    predicate CreateAliasEnsuresPublicly(input: CreateAliasRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method CreateAlias ( input: CreateAliasRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateAlias
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateAliasEnsuresPublicly(input, output)
      ensures History.CreateAlias == old(History.CreateAlias) + [DafnyCallEvent(input, output)]

    predicate CreateCustomKeyStoreEnsuresPublicly(input: CreateCustomKeyStoreRequest , output: Result<CreateCustomKeyStoreResponse, Error>)
    // The public method to be called by library consumers
    method CreateCustomKeyStore ( input: CreateCustomKeyStoreRequest )
      returns (output: Result<CreateCustomKeyStoreResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateCustomKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.CreateCustomKeyStore == old(History.CreateCustomKeyStore) + [DafnyCallEvent(input, output)]

    predicate CreateGrantEnsuresPublicly(input: CreateGrantRequest , output: Result<CreateGrantResponse, Error>)
    // The public method to be called by library consumers
    method CreateGrant ( input: CreateGrantRequest )
      returns (output: Result<CreateGrantResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateGrant
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateGrantEnsuresPublicly(input, output)
      ensures History.CreateGrant == old(History.CreateGrant) + [DafnyCallEvent(input, output)]

    predicate CreateKeyEnsuresPublicly(input: CreateKeyRequest , output: Result<CreateKeyResponse, Error>)
    // The public method to be called by library consumers
    method CreateKey ( input: CreateKeyRequest )
      returns (output: Result<CreateKeyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`CreateKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures CreateKeyEnsuresPublicly(input, output)
      ensures History.CreateKey == old(History.CreateKey) + [DafnyCallEvent(input, output)]

    predicate DecryptEnsuresPublicly(input: DecryptRequest , output: Result<DecryptResponse, Error>)
    // The public method to be called by library consumers
    method Decrypt ( input: DecryptRequest )
      returns (output: Result<DecryptResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Decrypt
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DecryptEnsuresPublicly(input, output)
      ensures History.Decrypt == old(History.Decrypt) + [DafnyCallEvent(input, output)]

    predicate DeleteAliasEnsuresPublicly(input: DeleteAliasRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method DeleteAlias ( input: DeleteAliasRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteAlias
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteAliasEnsuresPublicly(input, output)
      ensures History.DeleteAlias == old(History.DeleteAlias) + [DafnyCallEvent(input, output)]

    predicate DeleteCustomKeyStoreEnsuresPublicly(input: DeleteCustomKeyStoreRequest , output: Result<DeleteCustomKeyStoreResponse, Error>)
    // The public method to be called by library consumers
    method DeleteCustomKeyStore ( input: DeleteCustomKeyStoreRequest )
      returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteCustomKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.DeleteCustomKeyStore == old(History.DeleteCustomKeyStore) + [DafnyCallEvent(input, output)]

    predicate DeleteImportedKeyMaterialEnsuresPublicly(input: DeleteImportedKeyMaterialRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method DeleteImportedKeyMaterial ( input: DeleteImportedKeyMaterialRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeleteImportedKeyMaterial
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeleteImportedKeyMaterialEnsuresPublicly(input, output)
      ensures History.DeleteImportedKeyMaterial == old(History.DeleteImportedKeyMaterial) + [DafnyCallEvent(input, output)]

    predicate DescribeCustomKeyStoresEnsuresPublicly(input: DescribeCustomKeyStoresRequest , output: Result<DescribeCustomKeyStoresResponse, Error>)
    // The public method to be called by library consumers
    method DescribeCustomKeyStores ( input: DescribeCustomKeyStoresRequest )
      returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeCustomKeyStores
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeCustomKeyStoresEnsuresPublicly(input, output)
      ensures History.DescribeCustomKeyStores == old(History.DescribeCustomKeyStores) + [DafnyCallEvent(input, output)]

    predicate DescribeKeyEnsuresPublicly(input: DescribeKeyRequest , output: Result<DescribeKeyResponse, Error>)
    // The public method to be called by library consumers
    method DescribeKey ( input: DescribeKeyRequest )
      returns (output: Result<DescribeKeyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DescribeKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DescribeKeyEnsuresPublicly(input, output)
      ensures History.DescribeKey == old(History.DescribeKey) + [DafnyCallEvent(input, output)]

    predicate DisableKeyEnsuresPublicly(input: DisableKeyRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method DisableKey ( input: DisableKeyRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DisableKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DisableKeyEnsuresPublicly(input, output)
      ensures History.DisableKey == old(History.DisableKey) + [DafnyCallEvent(input, output)]

    predicate DisableKeyRotationEnsuresPublicly(input: DisableKeyRotationRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method DisableKeyRotation ( input: DisableKeyRotationRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DisableKeyRotation
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DisableKeyRotationEnsuresPublicly(input, output)
      ensures History.DisableKeyRotation == old(History.DisableKeyRotation) + [DafnyCallEvent(input, output)]

    predicate DisconnectCustomKeyStoreEnsuresPublicly(input: DisconnectCustomKeyStoreRequest , output: Result<DisconnectCustomKeyStoreResponse, Error>)
    // The public method to be called by library consumers
    method DisconnectCustomKeyStore ( input: DisconnectCustomKeyStoreRequest )
      returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DisconnectCustomKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DisconnectCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.DisconnectCustomKeyStore == old(History.DisconnectCustomKeyStore) + [DafnyCallEvent(input, output)]

    predicate EnableKeyEnsuresPublicly(input: EnableKeyRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method EnableKey ( input: EnableKeyRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`EnableKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures EnableKeyEnsuresPublicly(input, output)
      ensures History.EnableKey == old(History.EnableKey) + [DafnyCallEvent(input, output)]

    predicate EnableKeyRotationEnsuresPublicly(input: EnableKeyRotationRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method EnableKeyRotation ( input: EnableKeyRotationRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`EnableKeyRotation
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures EnableKeyRotationEnsuresPublicly(input, output)
      ensures History.EnableKeyRotation == old(History.EnableKeyRotation) + [DafnyCallEvent(input, output)]

    predicate EncryptEnsuresPublicly(input: EncryptRequest , output: Result<EncryptResponse, Error>)
    // The public method to be called by library consumers
    method Encrypt ( input: EncryptRequest )
      returns (output: Result<EncryptResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Encrypt
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures EncryptEnsuresPublicly(input, output)
      ensures History.Encrypt == old(History.Encrypt) + [DafnyCallEvent(input, output)]

    predicate GenerateDataKeyEnsuresPublicly(input: GenerateDataKeyRequest , output: Result<GenerateDataKeyResponse, Error>)
    // The public method to be called by library consumers
    method GenerateDataKey ( input: GenerateDataKeyRequest )
      returns (output: Result<GenerateDataKeyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GenerateDataKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GenerateDataKeyEnsuresPublicly(input, output)
      ensures History.GenerateDataKey == old(History.GenerateDataKey) + [DafnyCallEvent(input, output)]

    predicate GenerateDataKeyPairEnsuresPublicly(input: GenerateDataKeyPairRequest , output: Result<GenerateDataKeyPairResponse, Error>)
    // The public method to be called by library consumers
    method GenerateDataKeyPair ( input: GenerateDataKeyPairRequest )
      returns (output: Result<GenerateDataKeyPairResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GenerateDataKeyPair
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GenerateDataKeyPairEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyPair == old(History.GenerateDataKeyPair) + [DafnyCallEvent(input, output)]

    predicate GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyPairWithoutPlaintextRequest , output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
    // The public method to be called by library consumers
    method GenerateDataKeyPairWithoutPlaintext ( input: GenerateDataKeyPairWithoutPlaintextRequest )
      returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GenerateDataKeyPairWithoutPlaintext
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyPairWithoutPlaintext == old(History.GenerateDataKeyPairWithoutPlaintext) + [DafnyCallEvent(input, output)]

    predicate GenerateDataKeyWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyWithoutPlaintextRequest , output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
    // The public method to be called by library consumers
    method GenerateDataKeyWithoutPlaintext ( input: GenerateDataKeyWithoutPlaintextRequest )
      returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GenerateDataKeyWithoutPlaintext
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GenerateDataKeyWithoutPlaintextEnsuresPublicly(input, output)
      ensures History.GenerateDataKeyWithoutPlaintext == old(History.GenerateDataKeyWithoutPlaintext) + [DafnyCallEvent(input, output)]

    predicate GenerateRandomEnsuresPublicly(input: GenerateRandomRequest , output: Result<GenerateRandomResponse, Error>)
    // The public method to be called by library consumers
    method GenerateRandom ( input: GenerateRandomRequest )
      returns (output: Result<GenerateRandomResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GenerateRandom
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GenerateRandomEnsuresPublicly(input, output)
      ensures History.GenerateRandom == old(History.GenerateRandom) + [DafnyCallEvent(input, output)]

    predicate GetKeyPolicyEnsuresPublicly(input: GetKeyPolicyRequest , output: Result<GetKeyPolicyResponse, Error>)
    // The public method to be called by library consumers
    method GetKeyPolicy ( input: GetKeyPolicyRequest )
      returns (output: Result<GetKeyPolicyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetKeyPolicy
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetKeyPolicyEnsuresPublicly(input, output)
      ensures History.GetKeyPolicy == old(History.GetKeyPolicy) + [DafnyCallEvent(input, output)]

    predicate GetKeyRotationStatusEnsuresPublicly(input: GetKeyRotationStatusRequest , output: Result<GetKeyRotationStatusResponse, Error>)
    // The public method to be called by library consumers
    method GetKeyRotationStatus ( input: GetKeyRotationStatusRequest )
      returns (output: Result<GetKeyRotationStatusResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetKeyRotationStatus
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetKeyRotationStatusEnsuresPublicly(input, output)
      ensures History.GetKeyRotationStatus == old(History.GetKeyRotationStatus) + [DafnyCallEvent(input, output)]

    predicate GetParametersForImportEnsuresPublicly(input: GetParametersForImportRequest , output: Result<GetParametersForImportResponse, Error>)
    // The public method to be called by library consumers
    method GetParametersForImport ( input: GetParametersForImportRequest )
      returns (output: Result<GetParametersForImportResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetParametersForImport
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetParametersForImportEnsuresPublicly(input, output)
      ensures History.GetParametersForImport == old(History.GetParametersForImport) + [DafnyCallEvent(input, output)]

    predicate GetPublicKeyEnsuresPublicly(input: GetPublicKeyRequest , output: Result<GetPublicKeyResponse, Error>)
    // The public method to be called by library consumers
    method GetPublicKey ( input: GetPublicKeyRequest )
      returns (output: Result<GetPublicKeyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`GetPublicKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures GetPublicKeyEnsuresPublicly(input, output)
      ensures History.GetPublicKey == old(History.GetPublicKey) + [DafnyCallEvent(input, output)]

    predicate ImportKeyMaterialEnsuresPublicly(input: ImportKeyMaterialRequest , output: Result<ImportKeyMaterialResponse, Error>)
    // The public method to be called by library consumers
    method ImportKeyMaterial ( input: ImportKeyMaterialRequest )
      returns (output: Result<ImportKeyMaterialResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ImportKeyMaterial
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ImportKeyMaterialEnsuresPublicly(input, output)
      ensures History.ImportKeyMaterial == old(History.ImportKeyMaterial) + [DafnyCallEvent(input, output)]

    predicate ListAliasesEnsuresPublicly(input: ListAliasesRequest , output: Result<ListAliasesResponse, Error>)
    // The public method to be called by library consumers
    method ListAliases ( input: ListAliasesRequest )
      returns (output: Result<ListAliasesResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListAliases
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListAliasesEnsuresPublicly(input, output)
      ensures History.ListAliases == old(History.ListAliases) + [DafnyCallEvent(input, output)]

    predicate ListGrantsEnsuresPublicly(input: ListGrantsRequest , output: Result<ListGrantsResponse, Error>)
    // The public method to be called by library consumers
    method ListGrants ( input: ListGrantsRequest )
      returns (output: Result<ListGrantsResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListGrants
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListGrantsEnsuresPublicly(input, output)
      ensures History.ListGrants == old(History.ListGrants) + [DafnyCallEvent(input, output)]

    predicate ListKeyPoliciesEnsuresPublicly(input: ListKeyPoliciesRequest , output: Result<ListKeyPoliciesResponse, Error>)
    // The public method to be called by library consumers
    method ListKeyPolicies ( input: ListKeyPoliciesRequest )
      returns (output: Result<ListKeyPoliciesResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListKeyPolicies
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListKeyPoliciesEnsuresPublicly(input, output)
      ensures History.ListKeyPolicies == old(History.ListKeyPolicies) + [DafnyCallEvent(input, output)]

    predicate ListResourceTagsEnsuresPublicly(input: ListResourceTagsRequest , output: Result<ListResourceTagsResponse, Error>)
    // The public method to be called by library consumers
    method ListResourceTags ( input: ListResourceTagsRequest )
      returns (output: Result<ListResourceTagsResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ListResourceTags
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ListResourceTagsEnsuresPublicly(input, output)
      ensures History.ListResourceTags == old(History.ListResourceTags) + [DafnyCallEvent(input, output)]

    predicate PutKeyPolicyEnsuresPublicly(input: PutKeyPolicyRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method PutKeyPolicy ( input: PutKeyPolicyRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`PutKeyPolicy
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures PutKeyPolicyEnsuresPublicly(input, output)
      ensures History.PutKeyPolicy == old(History.PutKeyPolicy) + [DafnyCallEvent(input, output)]

    predicate ReEncryptEnsuresPublicly(input: ReEncryptRequest , output: Result<ReEncryptResponse, Error>)
    // The public method to be called by library consumers
    method ReEncrypt ( input: ReEncryptRequest )
      returns (output: Result<ReEncryptResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ReEncrypt
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ReEncryptEnsuresPublicly(input, output)
      ensures History.ReEncrypt == old(History.ReEncrypt) + [DafnyCallEvent(input, output)]

    predicate ReplicateKeyEnsuresPublicly(input: ReplicateKeyRequest , output: Result<ReplicateKeyResponse, Error>)
    // The public method to be called by library consumers
    method ReplicateKey ( input: ReplicateKeyRequest )
      returns (output: Result<ReplicateKeyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ReplicateKey
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ReplicateKeyEnsuresPublicly(input, output)
      ensures History.ReplicateKey == old(History.ReplicateKey) + [DafnyCallEvent(input, output)]

    predicate RetireGrantEnsuresPublicly(input: RetireGrantRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method RetireGrant ( input: RetireGrantRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`RetireGrant
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures RetireGrantEnsuresPublicly(input, output)
      ensures History.RetireGrant == old(History.RetireGrant) + [DafnyCallEvent(input, output)]

    predicate RevokeGrantEnsuresPublicly(input: RevokeGrantRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method RevokeGrant ( input: RevokeGrantRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`RevokeGrant
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures RevokeGrantEnsuresPublicly(input, output)
      ensures History.RevokeGrant == old(History.RevokeGrant) + [DafnyCallEvent(input, output)]

    predicate ScheduleKeyDeletionEnsuresPublicly(input: ScheduleKeyDeletionRequest , output: Result<ScheduleKeyDeletionResponse, Error>)
    // The public method to be called by library consumers
    method ScheduleKeyDeletion ( input: ScheduleKeyDeletionRequest )
      returns (output: Result<ScheduleKeyDeletionResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`ScheduleKeyDeletion
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures ScheduleKeyDeletionEnsuresPublicly(input, output)
      ensures History.ScheduleKeyDeletion == old(History.ScheduleKeyDeletion) + [DafnyCallEvent(input, output)]

    predicate SignEnsuresPublicly(input: SignRequest , output: Result<SignResponse, Error>)
    // The public method to be called by library consumers
    method Sign ( input: SignRequest )
      returns (output: Result<SignResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Sign
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures SignEnsuresPublicly(input, output)
      ensures History.Sign == old(History.Sign) + [DafnyCallEvent(input, output)]

    predicate TagResourceEnsuresPublicly(input: TagResourceRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method TagResource ( input: TagResourceRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`TagResource
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures TagResourceEnsuresPublicly(input, output)
      ensures History.TagResource == old(History.TagResource) + [DafnyCallEvent(input, output)]

    predicate UntagResourceEnsuresPublicly(input: UntagResourceRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method UntagResource ( input: UntagResourceRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UntagResource
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UntagResourceEnsuresPublicly(input, output)
      ensures History.UntagResource == old(History.UntagResource) + [DafnyCallEvent(input, output)]

    predicate UpdateAliasEnsuresPublicly(input: UpdateAliasRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method UpdateAlias ( input: UpdateAliasRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateAlias
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateAliasEnsuresPublicly(input, output)
      ensures History.UpdateAlias == old(History.UpdateAlias) + [DafnyCallEvent(input, output)]

    predicate UpdateCustomKeyStoreEnsuresPublicly(input: UpdateCustomKeyStoreRequest , output: Result<UpdateCustomKeyStoreResponse, Error>)
    // The public method to be called by library consumers
    method UpdateCustomKeyStore ( input: UpdateCustomKeyStoreRequest )
      returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateCustomKeyStore
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateCustomKeyStoreEnsuresPublicly(input, output)
      ensures History.UpdateCustomKeyStore == old(History.UpdateCustomKeyStore) + [DafnyCallEvent(input, output)]

    predicate UpdateKeyDescriptionEnsuresPublicly(input: UpdateKeyDescriptionRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method UpdateKeyDescription ( input: UpdateKeyDescriptionRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdateKeyDescription
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdateKeyDescriptionEnsuresPublicly(input, output)
      ensures History.UpdateKeyDescription == old(History.UpdateKeyDescription) + [DafnyCallEvent(input, output)]

    predicate UpdatePrimaryRegionEnsuresPublicly(input: UpdatePrimaryRegionRequest , output: Result<(), Error>)
    // The public method to be called by library consumers
    method UpdatePrimaryRegion ( input: UpdatePrimaryRegionRequest )
      returns (output: Result<(), Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`UpdatePrimaryRegion
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures UpdatePrimaryRegionEnsuresPublicly(input, output)
      ensures History.UpdatePrimaryRegion == old(History.UpdatePrimaryRegion) + [DafnyCallEvent(input, output)]

    predicate VerifyEnsuresPublicly(input: VerifyRequest , output: Result<VerifyResponse, Error>)
    // The public method to be called by library consumers
    method Verify ( input: VerifyRequest )
      returns (output: Result<VerifyResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`Verify
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures VerifyEnsuresPublicly(input, output)
      ensures History.Verify == old(History.Verify) + [DafnyCallEvent(input, output)]

  }
  type TrustAnchorCertificateType = x: string | IsValid_TrustAnchorCertificateType(x) witness *
  predicate method IsValid_TrustAnchorCertificateType(x: string) {
    ( 1 <= |x| <= 5000 )
  }
  datatype UntagResourceRequest = | UntagResourceRequest (
    nameonly KeyId: KeyIdType ,
    nameonly TagKeys: TagKeyList
  )
  datatype UpdateAliasRequest = | UpdateAliasRequest (
    nameonly AliasName: AliasNameType ,
    nameonly TargetKeyId: KeyIdType
  )
  datatype UpdateCustomKeyStoreRequest = | UpdateCustomKeyStoreRequest (
    nameonly CustomKeyStoreId: CustomKeyStoreIdType ,
    nameonly NewCustomKeyStoreName: Option<CustomKeyStoreNameType> := Option.None ,
    nameonly KeyStorePassword: Option<KeyStorePasswordType> := Option.None ,
    nameonly CloudHsmClusterId: Option<CloudHsmClusterIdType> := Option.None
  )
  datatype UpdateCustomKeyStoreResponse = | UpdateCustomKeyStoreResponse (

                                          )
  datatype UpdateKeyDescriptionRequest = | UpdateKeyDescriptionRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Description: DescriptionType
  )
  datatype UpdatePrimaryRegionRequest = | UpdatePrimaryRegionRequest (
    nameonly KeyId: KeyIdType ,
    nameonly PrimaryRegion: RegionType
  )
  datatype VerifyRequest = | VerifyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly Message: PlaintextType ,
    nameonly MessageType: Option<MessageType> := Option.None ,
    nameonly Signature: CiphertextType ,
    nameonly SigningAlgorithm: SigningAlgorithmSpec ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None
  )
  datatype VerifyResponse = | VerifyResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly SignatureValid: Option<BooleanType> := Option.None ,
    nameonly SigningAlgorithm: Option<SigningAlgorithmSpec> := Option.None
  )
  datatype WrappingKeySpec =
    | RSA_2048
  datatype Error =
      // Local Error structures are listed here
    | AlreadyExistsException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CloudHsmClusterInUseException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CloudHsmClusterInvalidConfigurationException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CloudHsmClusterNotActiveException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CloudHsmClusterNotFoundException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CloudHsmClusterNotRelatedException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CustomKeyStoreHasCMKsException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CustomKeyStoreInvalidStateException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CustomKeyStoreNameInUseException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | CustomKeyStoreNotFoundException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | DependencyTimeoutException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | DisabledException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | ExpiredImportTokenException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | IncorrectKeyException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | IncorrectKeyMaterialException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | IncorrectTrustAnchorException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidAliasNameException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidArnException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidCiphertextException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidGrantIdException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidGrantTokenException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidImportTokenException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidKeyUsageException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidMarkerException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KeyUnavailableException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KMSInternalException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KMSInvalidSignatureException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KMSInvalidStateException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | LimitExceededException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | MalformedPolicyDocumentException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | NotFoundException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | TagException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | UnsupportedOperationException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
      // Any dependent models are listed here


      // The Opaque error, used for native, extern, wrapped or unknown errors
    | Opaque(obj: object)
  type OpaqueError = e: Error | e.Opaque? witness *
}
abstract module AbstractComAmazonawsKmsService {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
  import opened Types = ComAmazonawsKmsTypes
  datatype KMSClientConfigType = KMSClientConfigType
  function method DefaultKMSClientConfigType(): KMSClientConfigType
  method {:extern} KMSClient()
    returns (res: Result<IKMSClient, Error>)
    ensures res.Success? ==>
              && fresh(res.value)
              && fresh(res.value.Modifies)
              && fresh(res.value.History)
              && res.value.ValidState()
  // Helper functions for the benefit of native code to create a Success(client) without referring to Dafny internals
  function method CreateSuccessOfClient(client: IKMSClient): Result<IKMSClient, Error> {
    Success(client)
  }
  function method CreateFailureOfError(error: Error): Result<IKMSClient, Error> {
    Failure(error)
  }
}
abstract module AbstractComAmazonawsKmsOperations {
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
  import opened Types = ComAmazonawsKmsTypes
  type InternalConfig
  predicate ValidInternalConfig?(config: InternalConfig)
  function ModifiesInternalConfig(config: InternalConfig): set<object>
  predicate CancelKeyDeletionEnsuresPublicly(input: CancelKeyDeletionRequest , output: Result<CancelKeyDeletionResponse, Error>)
  // The private method to be refined by the library developer


  method CancelKeyDeletion ( config: InternalConfig , input: CancelKeyDeletionRequest )
    returns (output: Result<CancelKeyDeletionResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CancelKeyDeletionEnsuresPublicly(input, output)


  predicate ConnectCustomKeyStoreEnsuresPublicly(input: ConnectCustomKeyStoreRequest , output: Result<ConnectCustomKeyStoreResponse, Error>)
  // The private method to be refined by the library developer


  method ConnectCustomKeyStore ( config: InternalConfig , input: ConnectCustomKeyStoreRequest )
    returns (output: Result<ConnectCustomKeyStoreResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ConnectCustomKeyStoreEnsuresPublicly(input, output)


  predicate CreateAliasEnsuresPublicly(input: CreateAliasRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method CreateAlias ( config: InternalConfig , input: CreateAliasRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateAliasEnsuresPublicly(input, output)


  predicate CreateCustomKeyStoreEnsuresPublicly(input: CreateCustomKeyStoreRequest , output: Result<CreateCustomKeyStoreResponse, Error>)
  // The private method to be refined by the library developer


  method CreateCustomKeyStore ( config: InternalConfig , input: CreateCustomKeyStoreRequest )
    returns (output: Result<CreateCustomKeyStoreResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateCustomKeyStoreEnsuresPublicly(input, output)


  predicate CreateGrantEnsuresPublicly(input: CreateGrantRequest , output: Result<CreateGrantResponse, Error>)
  // The private method to be refined by the library developer


  method CreateGrant ( config: InternalConfig , input: CreateGrantRequest )
    returns (output: Result<CreateGrantResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateGrantEnsuresPublicly(input, output)


  predicate CreateKeyEnsuresPublicly(input: CreateKeyRequest , output: Result<CreateKeyResponse, Error>)
  // The private method to be refined by the library developer


  method CreateKey ( config: InternalConfig , input: CreateKeyRequest )
    returns (output: Result<CreateKeyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures CreateKeyEnsuresPublicly(input, output)


  predicate DecryptEnsuresPublicly(input: DecryptRequest , output: Result<DecryptResponse, Error>)
  // The private method to be refined by the library developer


  method Decrypt ( config: InternalConfig , input: DecryptRequest )
    returns (output: Result<DecryptResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DecryptEnsuresPublicly(input, output)


  predicate DeleteAliasEnsuresPublicly(input: DeleteAliasRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method DeleteAlias ( config: InternalConfig , input: DeleteAliasRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteAliasEnsuresPublicly(input, output)


  predicate DeleteCustomKeyStoreEnsuresPublicly(input: DeleteCustomKeyStoreRequest , output: Result<DeleteCustomKeyStoreResponse, Error>)
  // The private method to be refined by the library developer


  method DeleteCustomKeyStore ( config: InternalConfig , input: DeleteCustomKeyStoreRequest )
    returns (output: Result<DeleteCustomKeyStoreResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteCustomKeyStoreEnsuresPublicly(input, output)


  predicate DeleteImportedKeyMaterialEnsuresPublicly(input: DeleteImportedKeyMaterialRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method DeleteImportedKeyMaterial ( config: InternalConfig , input: DeleteImportedKeyMaterialRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeleteImportedKeyMaterialEnsuresPublicly(input, output)


  predicate DescribeCustomKeyStoresEnsuresPublicly(input: DescribeCustomKeyStoresRequest , output: Result<DescribeCustomKeyStoresResponse, Error>)
  // The private method to be refined by the library developer


  method DescribeCustomKeyStores ( config: InternalConfig , input: DescribeCustomKeyStoresRequest )
    returns (output: Result<DescribeCustomKeyStoresResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeCustomKeyStoresEnsuresPublicly(input, output)


  predicate DescribeKeyEnsuresPublicly(input: DescribeKeyRequest , output: Result<DescribeKeyResponse, Error>)
  // The private method to be refined by the library developer


  method DescribeKey ( config: InternalConfig , input: DescribeKeyRequest )
    returns (output: Result<DescribeKeyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DescribeKeyEnsuresPublicly(input, output)


  predicate DisableKeyEnsuresPublicly(input: DisableKeyRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method DisableKey ( config: InternalConfig , input: DisableKeyRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DisableKeyEnsuresPublicly(input, output)


  predicate DisableKeyRotationEnsuresPublicly(input: DisableKeyRotationRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method DisableKeyRotation ( config: InternalConfig , input: DisableKeyRotationRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DisableKeyRotationEnsuresPublicly(input, output)


  predicate DisconnectCustomKeyStoreEnsuresPublicly(input: DisconnectCustomKeyStoreRequest , output: Result<DisconnectCustomKeyStoreResponse, Error>)
  // The private method to be refined by the library developer


  method DisconnectCustomKeyStore ( config: InternalConfig , input: DisconnectCustomKeyStoreRequest )
    returns (output: Result<DisconnectCustomKeyStoreResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DisconnectCustomKeyStoreEnsuresPublicly(input, output)


  predicate EnableKeyEnsuresPublicly(input: EnableKeyRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method EnableKey ( config: InternalConfig , input: EnableKeyRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures EnableKeyEnsuresPublicly(input, output)


  predicate EnableKeyRotationEnsuresPublicly(input: EnableKeyRotationRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method EnableKeyRotation ( config: InternalConfig , input: EnableKeyRotationRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures EnableKeyRotationEnsuresPublicly(input, output)


  predicate EncryptEnsuresPublicly(input: EncryptRequest , output: Result<EncryptResponse, Error>)
  // The private method to be refined by the library developer


  method Encrypt ( config: InternalConfig , input: EncryptRequest )
    returns (output: Result<EncryptResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures EncryptEnsuresPublicly(input, output)


  predicate GenerateDataKeyEnsuresPublicly(input: GenerateDataKeyRequest , output: Result<GenerateDataKeyResponse, Error>)
  // The private method to be refined by the library developer


  method GenerateDataKey ( config: InternalConfig , input: GenerateDataKeyRequest )
    returns (output: Result<GenerateDataKeyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GenerateDataKeyEnsuresPublicly(input, output)


  predicate GenerateDataKeyPairEnsuresPublicly(input: GenerateDataKeyPairRequest , output: Result<GenerateDataKeyPairResponse, Error>)
  // The private method to be refined by the library developer


  method GenerateDataKeyPair ( config: InternalConfig , input: GenerateDataKeyPairRequest )
    returns (output: Result<GenerateDataKeyPairResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GenerateDataKeyPairEnsuresPublicly(input, output)


  predicate GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyPairWithoutPlaintextRequest , output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
  // The private method to be refined by the library developer


  method GenerateDataKeyPairWithoutPlaintext ( config: InternalConfig , input: GenerateDataKeyPairWithoutPlaintextRequest )
    returns (output: Result<GenerateDataKeyPairWithoutPlaintextResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GenerateDataKeyPairWithoutPlaintextEnsuresPublicly(input, output)


  predicate GenerateDataKeyWithoutPlaintextEnsuresPublicly(input: GenerateDataKeyWithoutPlaintextRequest , output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
  // The private method to be refined by the library developer


  method GenerateDataKeyWithoutPlaintext ( config: InternalConfig , input: GenerateDataKeyWithoutPlaintextRequest )
    returns (output: Result<GenerateDataKeyWithoutPlaintextResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GenerateDataKeyWithoutPlaintextEnsuresPublicly(input, output)


  predicate GenerateRandomEnsuresPublicly(input: GenerateRandomRequest , output: Result<GenerateRandomResponse, Error>)
  // The private method to be refined by the library developer


  method GenerateRandom ( config: InternalConfig , input: GenerateRandomRequest )
    returns (output: Result<GenerateRandomResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GenerateRandomEnsuresPublicly(input, output)


  predicate GetKeyPolicyEnsuresPublicly(input: GetKeyPolicyRequest , output: Result<GetKeyPolicyResponse, Error>)
  // The private method to be refined by the library developer


  method GetKeyPolicy ( config: InternalConfig , input: GetKeyPolicyRequest )
    returns (output: Result<GetKeyPolicyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GetKeyPolicyEnsuresPublicly(input, output)


  predicate GetKeyRotationStatusEnsuresPublicly(input: GetKeyRotationStatusRequest , output: Result<GetKeyRotationStatusResponse, Error>)
  // The private method to be refined by the library developer


  method GetKeyRotationStatus ( config: InternalConfig , input: GetKeyRotationStatusRequest )
    returns (output: Result<GetKeyRotationStatusResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GetKeyRotationStatusEnsuresPublicly(input, output)


  predicate GetParametersForImportEnsuresPublicly(input: GetParametersForImportRequest , output: Result<GetParametersForImportResponse, Error>)
  // The private method to be refined by the library developer


  method GetParametersForImport ( config: InternalConfig , input: GetParametersForImportRequest )
    returns (output: Result<GetParametersForImportResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GetParametersForImportEnsuresPublicly(input, output)


  predicate GetPublicKeyEnsuresPublicly(input: GetPublicKeyRequest , output: Result<GetPublicKeyResponse, Error>)
  // The private method to be refined by the library developer


  method GetPublicKey ( config: InternalConfig , input: GetPublicKeyRequest )
    returns (output: Result<GetPublicKeyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures GetPublicKeyEnsuresPublicly(input, output)


  predicate ImportKeyMaterialEnsuresPublicly(input: ImportKeyMaterialRequest , output: Result<ImportKeyMaterialResponse, Error>)
  // The private method to be refined by the library developer


  method ImportKeyMaterial ( config: InternalConfig , input: ImportKeyMaterialRequest )
    returns (output: Result<ImportKeyMaterialResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ImportKeyMaterialEnsuresPublicly(input, output)


  predicate ListAliasesEnsuresPublicly(input: ListAliasesRequest , output: Result<ListAliasesResponse, Error>)
  // The private method to be refined by the library developer


  method ListAliases ( config: InternalConfig , input: ListAliasesRequest )
    returns (output: Result<ListAliasesResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListAliasesEnsuresPublicly(input, output)


  predicate ListGrantsEnsuresPublicly(input: ListGrantsRequest , output: Result<ListGrantsResponse, Error>)
  // The private method to be refined by the library developer


  method ListGrants ( config: InternalConfig , input: ListGrantsRequest )
    returns (output: Result<ListGrantsResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListGrantsEnsuresPublicly(input, output)


  predicate ListKeyPoliciesEnsuresPublicly(input: ListKeyPoliciesRequest , output: Result<ListKeyPoliciesResponse, Error>)
  // The private method to be refined by the library developer


  method ListKeyPolicies ( config: InternalConfig , input: ListKeyPoliciesRequest )
    returns (output: Result<ListKeyPoliciesResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListKeyPoliciesEnsuresPublicly(input, output)


  predicate ListResourceTagsEnsuresPublicly(input: ListResourceTagsRequest , output: Result<ListResourceTagsResponse, Error>)
  // The private method to be refined by the library developer


  method ListResourceTags ( config: InternalConfig , input: ListResourceTagsRequest )
    returns (output: Result<ListResourceTagsResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ListResourceTagsEnsuresPublicly(input, output)


  predicate PutKeyPolicyEnsuresPublicly(input: PutKeyPolicyRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method PutKeyPolicy ( config: InternalConfig , input: PutKeyPolicyRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures PutKeyPolicyEnsuresPublicly(input, output)


  predicate ReEncryptEnsuresPublicly(input: ReEncryptRequest , output: Result<ReEncryptResponse, Error>)
  // The private method to be refined by the library developer


  method ReEncrypt ( config: InternalConfig , input: ReEncryptRequest )
    returns (output: Result<ReEncryptResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ReEncryptEnsuresPublicly(input, output)


  predicate ReplicateKeyEnsuresPublicly(input: ReplicateKeyRequest , output: Result<ReplicateKeyResponse, Error>)
  // The private method to be refined by the library developer


  method ReplicateKey ( config: InternalConfig , input: ReplicateKeyRequest )
    returns (output: Result<ReplicateKeyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ReplicateKeyEnsuresPublicly(input, output)


  predicate RetireGrantEnsuresPublicly(input: RetireGrantRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method RetireGrant ( config: InternalConfig , input: RetireGrantRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures RetireGrantEnsuresPublicly(input, output)


  predicate RevokeGrantEnsuresPublicly(input: RevokeGrantRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method RevokeGrant ( config: InternalConfig , input: RevokeGrantRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures RevokeGrantEnsuresPublicly(input, output)


  predicate ScheduleKeyDeletionEnsuresPublicly(input: ScheduleKeyDeletionRequest , output: Result<ScheduleKeyDeletionResponse, Error>)
  // The private method to be refined by the library developer


  method ScheduleKeyDeletion ( config: InternalConfig , input: ScheduleKeyDeletionRequest )
    returns (output: Result<ScheduleKeyDeletionResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures ScheduleKeyDeletionEnsuresPublicly(input, output)


  predicate SignEnsuresPublicly(input: SignRequest , output: Result<SignResponse, Error>)
  // The private method to be refined by the library developer


  method Sign ( config: InternalConfig , input: SignRequest )
    returns (output: Result<SignResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures SignEnsuresPublicly(input, output)


  predicate TagResourceEnsuresPublicly(input: TagResourceRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method TagResource ( config: InternalConfig , input: TagResourceRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures TagResourceEnsuresPublicly(input, output)


  predicate UntagResourceEnsuresPublicly(input: UntagResourceRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method UntagResource ( config: InternalConfig , input: UntagResourceRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UntagResourceEnsuresPublicly(input, output)


  predicate UpdateAliasEnsuresPublicly(input: UpdateAliasRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method UpdateAlias ( config: InternalConfig , input: UpdateAliasRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateAliasEnsuresPublicly(input, output)


  predicate UpdateCustomKeyStoreEnsuresPublicly(input: UpdateCustomKeyStoreRequest , output: Result<UpdateCustomKeyStoreResponse, Error>)
  // The private method to be refined by the library developer


  method UpdateCustomKeyStore ( config: InternalConfig , input: UpdateCustomKeyStoreRequest )
    returns (output: Result<UpdateCustomKeyStoreResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateCustomKeyStoreEnsuresPublicly(input, output)


  predicate UpdateKeyDescriptionEnsuresPublicly(input: UpdateKeyDescriptionRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method UpdateKeyDescription ( config: InternalConfig , input: UpdateKeyDescriptionRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdateKeyDescriptionEnsuresPublicly(input, output)


  predicate UpdatePrimaryRegionEnsuresPublicly(input: UpdatePrimaryRegionRequest , output: Result<(), Error>)
  // The private method to be refined by the library developer


  method UpdatePrimaryRegion ( config: InternalConfig , input: UpdatePrimaryRegionRequest )
    returns (output: Result<(), Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures UpdatePrimaryRegionEnsuresPublicly(input, output)


  predicate VerifyEnsuresPublicly(input: VerifyRequest , output: Result<VerifyResponse, Error>)
  // The private method to be refined by the library developer


  method Verify ( config: InternalConfig , input: VerifyRequest )
    returns (output: Result<VerifyResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures VerifyEnsuresPublicly(input, output)
}
