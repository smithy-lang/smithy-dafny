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
    CreateWappedTestVectorKeyring,
    GetKeyDescription,
    SerializeKeyDescription,
  ]
}

structure KeyVectorsConfig {
  @required
  keyManifiestPath: String
}

operation CreateTestVectorKeyring {
  input: TestVectorKeyringInput,
  output: aws.cryptography.materialProviders#CreateKeyringOutput,
}

operation CreateWappedTestVectorKeyring {
  input: TestVectorKeyringInput,
  output: aws.cryptography.materialProviders#CreateKeyringOutput,
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
  keyDescription: KeyDescription
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


@error("client")
structure KeyVectorException {
  @required
  message: String,
}


