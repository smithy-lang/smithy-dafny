// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTestVectorKeysTypes.dfy"
  // Yes this is including from somewhere else.
include "../../TestVectorsAwsCryptographicMaterialProviders/src/LibraryIndex.dfy"
include "KeyringFromKeyDescription.dfy"

module {:options "-functionSyntax:4"} CmmFromKeyDescription {
  import opened Types = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import MPL = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import KeyringFromKeyDescription
  import UTF8
  import KeyMaterial

  method ToCmm(
    mpl: MPL.IAwsCryptographicMaterialProvidersClient,
    keys: map<string, KeyMaterial.KeyMaterial>,
    description: Types.KeyDescription,
    forOperation: CmmOperation
  )
    returns (output: Result<MPL.ICryptographicMaterialsManager, Error>)
    requires mpl.ValidState()
    modifies mpl.Modifies
    decreases description
    ensures mpl.ValidState()
    ensures output.Success? ==>
              && output.value.ValidState()
              && fresh(output.value.Modifies - mpl.Modifies)
              && output.value.Modifies !! {mpl.History}
  {
    var material := KeyringFromKeyDescription.GetKeyMaterial(keys, description);

    match description
    case RequiredEncryptionContext(cmm) => {
      var underlying :- ToCmm(mpl, keys, cmm.underlying, forOperation);
      var output' := mpl
      .CreateRequiredEncryptionContextCMM(
        MPL.CreateRequiredEncryptionContextCMMInput(
          underlyingCMM := Some(underlying),
          keyring := None,
          requiredEncryptionContextKeys := cmm.requiredEncryptionContextKeys
        )
      );
      output := output'.MapFailure(e => Types.AwsCryptographyMaterialProviders(e));
    }
    case _ => {
      var keyring :- KeyringFromKeyDescription.ToKeyring(mpl, keys, description);
      var output' := mpl
      .CreateDefaultCryptographicMaterialsManager(
        MPL.CreateDefaultCryptographicMaterialsManagerInput( keyring := keyring )
      );
      output := output'.MapFailure(e => Types.AwsCryptographyMaterialProviders(e));
    }
  }

}
