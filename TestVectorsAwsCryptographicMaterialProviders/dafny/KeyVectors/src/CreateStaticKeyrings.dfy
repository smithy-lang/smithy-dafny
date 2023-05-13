// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"

// This file creates intentinaly bad keyrings
// The goal here is to create keyrings
// that can verify that the CMM
// is really verifiying
// EncryptionMaterialsHasPlaintextDataKey
// ValidEncryptionMaterialsTransition
// DecryptionMaterialsTransitionIsValid
module CreateStaticKeyrings {
  import opened Wrappers
  import Types = AwsCryptographyMaterialProvidersTypes

  method CreateStaticMaterialsKeyring(
    encryptMaterial: Types.EncryptionMaterials,
    decryptMaterial: Types.DecryptionMaterials
  )
    returns (keyring: Types.IKeyring)
    ensures
      && keyring.ValidState()
      && fresh(keyring)
      && fresh(keyring.Modifies)
  {
    return new StaticMaterialsKeyring(encryptMaterial, decryptMaterial);
  }

  // The goal of this class is to return *static* materials.
  // The CMM MUST check that the materials it gets are valid
  // So this keyring can be configured to return materials
  // that MUST fail this check.
  // This is *NOT* at example of a properly desgined keyring!
  class StaticMaterialsKeyring
    extends Types.IKeyring
  {

    predicate ValidState()
      ensures ValidState() ==> History in Modifies
    {
      && History in Modifies
    }

    constructor (
      encryptMaterial: Types.EncryptionMaterials,
      decryptMaterial: Types.DecryptionMaterials
    )
      ensures ValidState() && fresh(this) && fresh(History) && fresh(Modifies)
    {
      History := new Types.IKeyringCallHistory();
      Modifies := {History};
      this.encryptMaterial := encryptMaterial;
      this.decryptMaterial := decryptMaterial;
    }

    const encryptMaterial: Types.EncryptionMaterials
    const decryptMaterial: Types.DecryptionMaterials

    predicate OnEncryptEnsuresPublicly ( input: Types.OnEncryptInput , output: Result<Types.OnEncryptOutput, Types.Error> ) {true}

    method OnEncrypt'(input: Types.OnEncryptInput)
      returns (res: Result<Types.OnEncryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnEncryptEnsuresPublicly(input, res)
      ensures unchanged(History)
    {
      return Success(Types.OnEncryptOutput(
                       materials := encryptMaterial
                     ));
    }

    predicate OnDecryptEnsuresPublicly ( input: Types.OnDecryptInput , output: Result<Types.OnDecryptOutput, Types.Error> ) {true}

    method OnDecrypt'(
      input: Types.OnDecryptInput
    )
      returns (res: Result<Types.OnDecryptOutput, Types.Error>)
      requires ValidState()
      modifies Modifies - {History}
      decreases Modifies - {History}
      ensures ValidState()
      ensures OnDecryptEnsuresPublicly(input, res)
      ensures unchanged(History)
    {
      return Success(Types.OnDecryptOutput(
                       materials := decryptMaterial
                     ));
    }
  }
}
