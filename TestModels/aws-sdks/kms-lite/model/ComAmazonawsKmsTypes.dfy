// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../dafny-dependencies/StandardLibrary/src/Index.dfy"
module {:extern "software.amazon.cryptography.services.kms.internaldafny.types" } ComAmazonawsKmsTypes
{
  import opened Wrappers
  import opened StandardLibrary.UInt
  import opened UTF8
    // Generic helpers for verification of mock/unit tests.
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  // Begin Generated Types

  type AttestationDocumentType = x: seq<uint8> | IsValid_AttestationDocumentType(x) witness *
  predicate method IsValid_AttestationDocumentType(x: seq<uint8>) {
    ( 1 <= |x| <= 262144 )
  }
  type CiphertextType = x: seq<uint8> | IsValid_CiphertextType(x) witness *
  predicate method IsValid_CiphertextType(x: seq<uint8>) {
    ( 1 <= |x| <= 6144 )
  }
  datatype CustomerMasterKeySpec =
    | RSA_2048
    | RSA_3072
    | RSA_4096
    | ECC_NIST_P256
    | ECC_NIST_P384
    | ECC_NIST_P521
    | ECC_SECG_P256K1
    | SYMMETRIC_DEFAULT
    | HMAC_224
    | HMAC_256
    | HMAC_384
    | HMAC_512
    | SM2
  datatype DataKeySpec =
    | AES_256
    | AES_128
  datatype DecryptRequest = | DecryptRequest (
    nameonly CiphertextBlob: CiphertextType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly Recipient: Option<RecipientInfo> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None
  )
  datatype DecryptResponse = | DecryptResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly Plaintext: Option<PlaintextType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly CiphertextForRecipient: Option<CiphertextType> := Option.None
  )
  datatype DeriveSharedSecretRequest = | DeriveSharedSecretRequest (
    nameonly KeyId: KeyIdType ,
    nameonly KeyAgreementAlgorithm: KeyAgreementAlgorithmSpec ,
    nameonly PublicKey: PublicKeyType ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None ,
    nameonly Recipient: Option<RecipientInfo> := Option.None
  )
  datatype DeriveSharedSecretResponse = | DeriveSharedSecretResponse (
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly SharedSecret: Option<PlaintextType> := Option.None ,
    nameonly CiphertextForRecipient: Option<CiphertextType> := Option.None ,
    nameonly KeyAgreementAlgorithm: Option<KeyAgreementAlgorithmSpec> := Option.None ,
    nameonly KeyOrigin: Option<OriginType> := Option.None
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
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None
  )
  datatype EncryptResponse = | EncryptResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly EncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None
  )
  type ErrorMessageType = string
  datatype GenerateDataKeyRequest = | GenerateDataKeyRequest (
    nameonly KeyId: KeyIdType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly NumberOfBytes: Option<NumberOfBytesType> := Option.None ,
    nameonly KeySpec: Option<DataKeySpec> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly Recipient: Option<RecipientInfo> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None
  )
  datatype GenerateDataKeyResponse = | GenerateDataKeyResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly Plaintext: Option<PlaintextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None ,
    nameonly CiphertextForRecipient: Option<CiphertextType> := Option.None
  )
  datatype GenerateDataKeyWithoutPlaintextRequest = | GenerateDataKeyWithoutPlaintextRequest (
    nameonly KeyId: KeyIdType ,
    nameonly EncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly KeySpec: Option<DataKeySpec> := Option.None ,
    nameonly NumberOfBytes: Option<NumberOfBytesType> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None
  )
  datatype GenerateDataKeyWithoutPlaintextResponse = | GenerateDataKeyWithoutPlaintextResponse (
    nameonly CiphertextBlob: Option<CiphertextType> := Option.None ,
    nameonly KeyId: Option<KeyIdType> := Option.None
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
    nameonly SigningAlgorithms: Option<SigningAlgorithmSpecList> := Option.None ,
    nameonly KeyAgreementAlgorithms: Option<KeyAgreementAlgorithmSpecList> := Option.None
  )
  type GrantTokenList = x: seq<GrantTokenType> | IsValid_GrantTokenList(x) witness *
  predicate method IsValid_GrantTokenList(x: seq<GrantTokenType>) {
    ( 0 <= |x| <= 10 )
  }
  type GrantTokenType = x: string | IsValid_GrantTokenType(x) witness *
  predicate method IsValid_GrantTokenType(x: string) {
    ( 1 <= |x| <= 8192 )
  }
  datatype KeyAgreementAlgorithmSpec =
    | ECDH
  type KeyAgreementAlgorithmSpecList = seq<KeyAgreementAlgorithmSpec>
  datatype KeyEncryptionMechanism =
    | RSAES_OAEP_SHA_256
  type KeyIdType = x: string | IsValid_KeyIdType(x) witness *
  predicate method IsValid_KeyIdType(x: string) {
    ( 1 <= |x| <= 2048 )
  }
  datatype KeySpec =
    | RSA_2048
    | RSA_3072
    | RSA_4096
    | ECC_NIST_P256
    | ECC_NIST_P384
    | ECC_NIST_P521
    | ECC_SECG_P256K1
    | SYMMETRIC_DEFAULT
    | HMAC_224
    | HMAC_256
    | HMAC_384
    | HMAC_512
    | SM2
  datatype KeyUsageType =
    | SIGN_VERIFY
    | ENCRYPT_DECRYPT
    | GENERATE_VERIFY_MAC
    | KEY_AGREEMENT
  type NullableBooleanType = bool
  type NumberOfBytesType = x: int32 | IsValid_NumberOfBytesType(x) witness *
  predicate method IsValid_NumberOfBytesType(x: int32) {
    ( 1 <= x <= 1024 )
  }
  datatype OriginType =
    | AWS_KMS
    | EXTERNAL
    | AWS_CLOUDHSM
    | EXTERNAL_KEY_STORE
  type PlaintextType = x: seq<uint8> | IsValid_PlaintextType(x) witness *
  predicate method IsValid_PlaintextType(x: seq<uint8>) {
    ( 1 <= |x| <= 4096 )
  }
  type PublicKeyType = x: seq<uint8> | IsValid_PublicKeyType(x) witness *
  predicate method IsValid_PublicKeyType(x: seq<uint8>) {
    ( 1 <= |x| <= 8192 )
  }
  datatype RecipientInfo = | RecipientInfo (
    nameonly KeyEncryptionAlgorithm: Option<KeyEncryptionMechanism> := Option.None ,
    nameonly AttestationDocument: Option<AttestationDocumentType> := Option.None
  )
  datatype ReEncryptRequest = | ReEncryptRequest (
    nameonly CiphertextBlob: CiphertextType ,
    nameonly SourceEncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly SourceKeyId: Option<KeyIdType> := Option.None ,
    nameonly DestinationKeyId: KeyIdType ,
    nameonly DestinationEncryptionContext: Option<EncryptionContextType> := Option.None ,
    nameonly SourceEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly DestinationEncryptionAlgorithm: Option<EncryptionAlgorithmSpec> := Option.None ,
    nameonly GrantTokens: Option<GrantTokenList> := Option.None ,
    nameonly DryRun: Option<NullableBooleanType> := Option.None
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
    | SM2DSA
  type SigningAlgorithmSpecList = seq<SigningAlgorithmSpec>
  class IKMSClientCallHistory {
    ghost constructor() {
      Decrypt := [];
      DeriveSharedSecret := [];
      Encrypt := [];
      GenerateDataKey := [];
      GenerateDataKeyWithoutPlaintext := [];
      GetPublicKey := [];
      ReEncrypt := [];
      UpdatePrimaryRegion := [];
    }
    ghost var Decrypt: seq<DafnyCallEvent<DecryptRequest, Result<DecryptResponse, Error>>>
    ghost var DeriveSharedSecret: seq<DafnyCallEvent<DeriveSharedSecretRequest, Result<DeriveSharedSecretResponse, Error>>>
    ghost var Encrypt: seq<DafnyCallEvent<EncryptRequest, Result<EncryptResponse, Error>>>
    ghost var GenerateDataKey: seq<DafnyCallEvent<GenerateDataKeyRequest, Result<GenerateDataKeyResponse, Error>>>
    ghost var GenerateDataKeyWithoutPlaintext: seq<DafnyCallEvent<GenerateDataKeyWithoutPlaintextRequest, Result<GenerateDataKeyWithoutPlaintextResponse, Error>>>
    ghost var GetPublicKey: seq<DafnyCallEvent<GetPublicKeyRequest, Result<GetPublicKeyResponse, Error>>>
    ghost var ReEncrypt: seq<DafnyCallEvent<ReEncryptRequest, Result<ReEncryptResponse, Error>>>
    ghost var UpdatePrimaryRegion: seq<DafnyCallEvent<UpdatePrimaryRegionRequest, Result<(), Error>>>
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

    predicate DeriveSharedSecretEnsuresPublicly(input: DeriveSharedSecretRequest , output: Result<DeriveSharedSecretResponse, Error>)
    // The public method to be called by library consumers
    method DeriveSharedSecret ( input: DeriveSharedSecretRequest )
      returns (output: Result<DeriveSharedSecretResponse, Error>)
      requires
        && ValidState()
      modifies Modifies - {History} ,
               History`DeriveSharedSecret
      // Dafny will skip type parameters when generating a default decreases clause.
      decreases Modifies - {History}
      ensures
        && ValidState()
      ensures DeriveSharedSecretEnsuresPublicly(input, output)
      ensures History.DeriveSharedSecret == old(History.DeriveSharedSecret) + [DafnyCallEvent(input, output)]

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

  }
  datatype UpdatePrimaryRegionRequest = | UpdatePrimaryRegionRequest (
    nameonly KeyId: KeyIdType ,
    nameonly PrimaryRegion: RegionType
  )
  datatype Error =
      // Local Error structures are listed here
    | DependencyTimeoutException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | DisabledException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | DryRunOperationException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | IncorrectKeyException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidArnException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidCiphertextException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidGrantTokenException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | InvalidKeyUsageException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KeyUnavailableException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KMSInternalException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | KMSInvalidStateException (
        nameonly message: Option<ErrorMessageType> := Option.None
      )
    | NotFoundException (
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


  predicate DeriveSharedSecretEnsuresPublicly(input: DeriveSharedSecretRequest , output: Result<DeriveSharedSecretResponse, Error>)
  // The private method to be refined by the library developer


  method DeriveSharedSecret ( config: InternalConfig , input: DeriveSharedSecretRequest )
    returns (output: Result<DeriveSharedSecretResponse, Error>)
    requires
      && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    // Dafny will skip type parameters when generating a default decreases clause.
    decreases ModifiesInternalConfig(config)
    ensures
      && ValidInternalConfig?(config)
    ensures DeriveSharedSecretEnsuresPublicly(input, output)


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
}
