namespace aws.cryptography.materialProviders

use aws.polymorph#reference
use aws.polymorph#positional
use aws.polymorph#extendable
use aws.polymorph#javadoc

//= aws-encryption-sdk-specification/framework/cmm-interface.md#supported-cmms
//= type=implication
//# Note: A user MAY create their own custom CMM.
@extendable
//= aws-encryption-sdk-specification/framework/cmm-interface.md#overview
//= type=implication
//# The CMM interface describes the interface that all CMMs MUST implement.
resource CryptographicMaterialsManager {
  //= aws-encryption-sdk-specification/framework/cmm-interface.md#behaviors
  //= type=implication
  //# The CMM Interface MUST support the following behaviors:
  operations: [GetEncryptionMaterials, DecryptMaterials]
}

/////////////////
// CMM Structures

@reference(resource: CryptographicMaterialsManager)
structure CryptographicMaterialsManagerReference {}

/////////////////
// CMM Operations

operation GetEncryptionMaterials {
  input: GetEncryptionMaterialsInput,
  output: GetEncryptionMaterialsOutput,
}

structure GetEncryptionMaterialsInput {
  //= aws-encryption-sdk-specification/framework/cmm-interface.md#encryption-materials-request
  //= type=implication
  //# The encryption materials request MUST include the following:
  //#   
  //# - [Encryption Context](structures.md#encryption-context)
  //#   - The encryption context provided MAY be empty.
  //# - [Commitment Policy](./commitment-policy.md#supported-commitment-policy-enum)

  @required
  encryptionContext: EncryptionContext,

  @required
  commitmentPolicy: CommitmentPolicy,

  //= aws-encryption-sdk-specification/framework/cmm-interface.md#encryption-materials-request
  //= type=implication
  //# The encryption request MAY include the following:
  //# 
  //# - [Algorithm Suite Id](algorithm-suites.md#algorithm-suite-id)
  //# - Required Encryption Context Keys - a set of strings.
  //# - Max Plaintext Length
  //#   - This value represents the maximum length of the plaintext to be encrypted
  //#     using the returned materials.
  //#     The length of the plaintext to be encrypted MUST not be larger than this value.

  algorithmSuiteId: AlgorithmSuiteId,

  maxPlaintextLength: Long,

  requiredEncryptionContextKeys: EncryptionContextKeys,
}

structure GetEncryptionMaterialsOutput {
  @required
  encryptionMaterials: EncryptionMaterials
}

operation DecryptMaterials {
  input: DecryptMaterialsInput,
  output: DecryptMaterialsOutput,
}

structure DecryptMaterialsInput {
//= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials-request
//= type=implication
//# The decrypt materials request MUST include the following:
//# 
//# - [Algorithm Suite Id](algorithm-suites.md#algorithm-suite-id)
//# - [Commitment Policy](./commitment-policy.md#supported-commitment-policy-enum)
//# - [Encrypted Data Keys](structures.md#encrypted-data-keys)
//# - [Encryption Context](structures.md#encryption-context)
//#   - The encryption context provided MAY be empty.

  @required
  algorithmSuiteId: AlgorithmSuiteId,

  @required
  commitmentPolicy: CommitmentPolicy,

  @required
  encryptedDataKeys: EncryptedDataKeyList,

  @required
  encryptionContext: EncryptionContext,

  //= aws-encryption-sdk-specification/framework/cmm-interface.md#decrypt-materials-request
  //= type=implication
  //# The decrypt materials request MAY include the following:
  //# 
  //# - [Reproduced Encryption Context](structures.md#encryption-context)

  reproducedEncryptionContext: EncryptionContext,
}

structure DecryptMaterialsOutput {
  @required
  decryptionMaterials: DecryptionMaterials 
}

///////////////////
// CMM Constructors

@positional
@javadoc("Outputs for creating a Default Cryptographic Materials Manager.")
structure CreateCryptographicMaterialsManagerOutput {
  @required
  @javadoc("The created Default Cryptographic Materials Manager.")
  materialsManager: CryptographicMaterialsManagerReference 
}

@javadoc("Creates a Default Cryptographic Materials Manager.")
operation CreateDefaultCryptographicMaterialsManager {
  input: CreateDefaultCryptographicMaterialsManagerInput,
  output: CreateCryptographicMaterialsManagerOutput,
}

@javadoc("Inputs for creating a Default Cryptographic Materials Manager.")
structure CreateDefaultCryptographicMaterialsManagerInput {
  @required
  @javadoc("The Keyring that the created Default Cryprographic Materials Manager will use to wrap data keys.")
  keyring: KeyringReference 
}

@positional
@javadoc("Outputs for creating an Required Encryption Context Cryptographic Materials Manager.")
structure CreateRequiredEncryptionContextCMMOutput {
  @required
  @javadoc("The created Required Encryption Context Cryptographic Materials Manager.")
  materialsManager: CryptographicMaterialsManagerReference
}

@javadoc("Creates an Required Encryption Context Cryptographic Materials Manager.")
operation CreateRequiredEncryptionContextCMM {
  input: CreateRequiredEncryptionContextCMMInput,
  output: CreateRequiredEncryptionContextCMMOutput,
}

@javadoc("Inputs for creating an Required Encryption Context Cryptographic Materials Manager.")
structure CreateRequiredEncryptionContextCMMInput {
  @javadoc("The Cryprographic Materials Manager that the created Required Encryption Context Cryptographic Materials Manager will delegate to. Either a Keyring or underlying Cryprographic Materials Manager must be specified.")
  underlyingCMM: CryptographicMaterialsManagerReference,
  @javadoc("The Keyring that the created Cryprographic Materials Manager will use to wrap data keys. The created Required Encryption Context CMM will delegate to a Default Cryptographic Materials Manager created with this Keyring. Either a Keyring or an underlying Cryprographic Materials Manager must be specified as input.")
  keyring: KeyringReference,
  @required
  @javadoc("A list of Encryption Context keys which are required to be supplied during encryption and decryption, and correspond to Encryption Context key-value pairs which are not stored on the resulting message.")
  requiredEncryptionContextKeys: EncryptionContextKeys
}
