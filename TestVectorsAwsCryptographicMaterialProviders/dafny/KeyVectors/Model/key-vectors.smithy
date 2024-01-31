namespace aws.cryptography.materialProvidersTestVectorKeys

/////////////
// KeyVectors Creation
@aws.polymorph#localService(
  sdkId: "KeyVectors",
  config: KeyVectorsConfig,
)
service KeyVectors {
  version: "20223-04-18",
  resources: [],
  operations: [
    CreateTestVectorKeyring,
    CreateWrappedTestVectorKeyring,
    CreateWrappedTestVectorCmm,
    GetKeyDescription,
    SerializeKeyDescription,
  ]
}

structure KeyVectorsConfig {
  @required
  keyManifestPath: String
}

operation CreateTestVectorKeyring {
  input: TestVectorKeyringInput,
  output: aws.cryptography.materialProviders#CreateKeyringOutput,
}

operation CreateWrappedTestVectorKeyring {
  input: TestVectorKeyringInput,
  output: aws.cryptography.materialProviders#CreateKeyringOutput,
}

operation CreateWrappedTestVectorCmm {
  input: TestVectorCmmInput,
  output: CreateWrappedTestVectorCmmOutput,
}

structure TestVectorCmmInput {
  @required
  keyDescription: KeyDescription,
  @required
  forOperation: CmmOperation,
}

@enum([
  {
    name: "ENCRYPT",
    value: "ENCRYPT",
  },
  {
    name: "DECRYPT",
    value: "DECRYPT",
  },
])
string CmmOperation

@aws.polymorph#positional
structure CreateWrappedTestVectorCmmOutput {
  @required
  cmm: aws.cryptography.materialProviders#CryptographicMaterialsManagerReference,
}

@readonly
operation GetKeyDescription {
  input: GetKeyDescriptionInput,
  output: GetKeyDescriptionOutput,
}
@readonly
operation SerializeKeyDescription {
  input: SerializeKeyDescriptionInput,
  output: SerializeKeyDescriptionOutput,
}

structure GetKeyDescriptionInput {
  @required
  json: Blob
}
structure GetKeyDescriptionOutput {
  @required
  keyDescription: KeyDescription
}

structure SerializeKeyDescriptionInput {
  @required
  keyDescription: KeyDescription
}

structure SerializeKeyDescriptionOutput {
  @required
  json: Blob
}

structure TestVectorKeyringInput {
  @required
  keyDescription: KeyDescription,
}

union KeyDescription {
  Kms: KMSInfo,
  KmsMrk: KmsMrkAware,
  KmsMrkDiscovery: KmsMrkAwareDiscovery,
  RSA: RawRSA,
  AES: RawAES,
  Static: StaticKeyring,
  KmsRsa: KmsRsaKeyring,
  Hierarchy: HierarchyKeyring,
  Multi: MultiKeyring,
  RequiredEncryptionContext: RequiredEncryptionContextCMM,
}

structure KMSInfo {
  @required
  keyId: String,
}
structure KmsMrkAware {
  @required
  keyId: String,
}
structure KmsMrkAwareDiscovery {
  @required
  keyId: String,
  @required
  defaultMrkRegion: String,
  awsKmsDiscoveryFilter: aws.cryptography.materialProviders#DiscoveryFilter,
}
structure RawRSA {
  @required
  keyId: String,
  @required
  providerId: String,
  @required
  padding: aws.cryptography.materialProviders#PaddingScheme,
}
structure RawAES {
  @required
  keyId: String,
  @required
  providerId: String,
}
structure StaticKeyring {
  @required
  keyId: String,
}

structure KmsRsaKeyring {
  @required
  keyId: String,
  @required
  encryptionAlgorithm: com.amazonaws.kms#EncryptionAlgorithmSpec,
}

structure HierarchyKeyring {
  @required
  keyId: String,
}

structure MultiKeyring {
  generator: KeyDescription,
  @required
  childKeyrings: KeyDescriptionList,
}

list KeyDescriptionList {
  member: KeyDescription
}

structure RequiredEncryptionContextCMM {
  @required
  underlying: KeyDescription,
  @required
  requiredEncryptionContextKeys: aws.cryptography.materialProviders#EncryptionContextKeys
}

@error("client")
structure KeyVectorException {
  @required
  message: String,
}


