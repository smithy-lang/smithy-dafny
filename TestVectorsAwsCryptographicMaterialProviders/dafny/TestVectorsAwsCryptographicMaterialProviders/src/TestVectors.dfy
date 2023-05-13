// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "CreateKeyrings.dfy"
include "../../KeyVectors/src/Index.dfy"

module {:options "-functionSyntax:4"} TestVectors {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders

  import opened Wrappers
  import opened StandardLibrary.UInt
  import UTF8

  import KeyVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  datatype EncryptTest = EncryptTest(
    input: Types.GetEncryptionMaterialsInput,
    cmm: Types.ICryptographicMaterialsManager,
    vector: EncryptTestVector
  )

  datatype DecryptTest = DecryptTest(
    input: Types.DecryptMaterialsInput,
    cmm: Types.ICryptographicMaterialsManager,
    vector: DecryptTestVector
  )

  method TestGetEncryptionMaterials(test: EncryptTest)
    returns (testResult: bool, materials: Option<Types.EncryptionMaterials>)
    requires test.cmm.ValidState()
    modifies test.cmm.Modifies
    ensures test.cmm.ValidState()
    ensures testResult && test.vector.PositiveEncryptKeyringVector? ==> materials.Some?
  {
    print "\nTEST===> ",
          test.vector.name,
          if test.vector.description.Some? then "\n" + test.vector.description.value else "",
          if test.vector.NegativeEncryptKeyringVector? then "\n" + test.vector.errorDescription else "", "\n";

    var result := test.cmm.GetEncryptionMaterials(test.input);

    testResult := match test.vector
      case PositiveEncryptKeyringVector(_,_,_,_,_,_,_,_,_)
        => result.Success?
      case NegativeEncryptKeyringVector(_,_,_,_,_,_,_,_,_)
        => !result.Success?;

    materials := if test.vector.PositiveEncryptKeyringVector? && result.Success? then
      Some(result.value.encryptionMaterials)
    else
      None;

    if !testResult {
      if test.vector.PositiveEncryptKeyringVector? {
        print result.error;
      }
      print "\nFAILED! <-----------\n";
    }
  }

  method TestDecryptMaterials(test: DecryptTest)
    returns (output: bool)
    requires test.cmm.ValidState()
    modifies test.cmm.Modifies
    ensures test.cmm.ValidState()
  {
    print "\nTEST===> ",
          test.vector.name,
          if test.vector.description.Some? then "\n" + test.vector.description.value else "",
          if test.vector.NegativeDecryptKeyringTest? then "\n" + test.vector.errorDescription else "\n";

    var result := test.cmm.DecryptMaterials(test.input);

    output := match test.vector
      case PositiveDecryptKeyringTest(_,_,_,_,_,_,_,_,_)
        // TODO need to verify the ouput. E.g. is the PTDK correct?
        =>
        && result.Success?
        && result.value.decryptionMaterials.plaintextDataKey == test.vector.expectedResult.plaintextDataKey
        && result.value.decryptionMaterials.symmetricSigningKey == test.vector.expectedResult.symmetricSigningKey
        && result.value.decryptionMaterials.requiredEncryptionContextKeys == test.vector.expectedResult.requiredEncryptionContextKeys
      case NegativeDecryptKeyringTest(_,_,_,_,_,_,_,_,_)
        => !result.Success?;

    if !output {
      if test.vector.PositiveDecryptKeyringTest? && result.Failure? {
        print result.error;
      }
      print "\nFAILED! <-----------\n";
    }
  }

  method ToEncryptTest(keys: KeyVectors.KeyVectorsClient, vector: EncryptTestVector)
    returns (output: Result<EncryptTest, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && output.value.cmm.ValidState()
              && fresh(output.value.cmm.Modifies)
  {
    var input := match vector
      case PositiveEncryptKeyringVector(
        _,_,
        encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys,
        _,_
        ) =>
        Types.GetEncryptionMaterialsInput(
          encryptionContext := encryptionContext,
          commitmentPolicy := commitmentPolicy,
          algorithmSuiteId := Some(algorithmSuite.id),
          maxPlaintextLength := maxPlaintextLength,
          requiredEncryptionContextKeys := requiredEncryptionContextKeys
        )
      case NegativeEncryptKeyringVector(
        _,_,
        encryptionContext, commitmentPolicy, algorithmSuite, maxPlaintextLength, requiredEncryptionContextKeys,
        _, _
        ) =>
        Types.GetEncryptionMaterialsInput(
          encryptionContext := encryptionContext,
          commitmentPolicy := commitmentPolicy,
          algorithmSuiteId := Some(algorithmSuite.id),
          maxPlaintextLength := maxPlaintextLength,
          requiredEncryptionContextKeys := requiredEncryptionContextKeys
        );

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var maybeKeyring := keys.CreateWappedTestVectorKeyring(
      KeyVectorsTypes.TestVectorKeyringInput(
        keyDescription := if vector.PositiveEncryptKeyringVector? then
          vector.encryptDescription
        else
          vector.keyDescription
      ));
    var keyring :- maybeKeyring.MapFailure((e: KeyVectorsTypes.Error) => var _ := printErr(e); "Keyring failure");

    var maybeCmm := mpl
    .CreateDefaultCryptographicMaterialsManager(
      Types.CreateDefaultCryptographicMaterialsManagerInput( keyring := keyring )
    );
    var cmm :- maybeCmm.MapFailure(e => "CMM failure");

    return Success(EncryptTest(
                     input := input,
                     cmm := cmm,
                     vector := vector
                   ));
  }

  method ToDecryptTest(keys: KeyVectors.KeyVectorsClient, test: EncryptTest, materials: Types.EncryptionMaterials)
    returns (output: Result<DecryptTest, string>)
    requires test.vector.PositiveEncryptKeyringVector?
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && output.value.cmm.ValidState()
              && fresh(output.value.cmm.Modifies)
  {

    // TODO remove requiredEncryptionContextKeys, and add to reproducedEncryptionContext
    var reproducedEncryptionContext := None;
    var input := Types.DecryptMaterialsInput(
      algorithmSuiteId := materials.algorithmSuite.id,
      commitmentPolicy := test.vector.commitmentPolicy,
      encryptedDataKeys := materials.encryptedDataKeys,
      encryptionContext := materials.encryptionContext,
      reproducedEncryptionContext := reproducedEncryptionContext
    );

    var vector := PositiveDecryptKeyringTest(
      name := test.vector.name + "->Decryption",
      algorithmSuite := materials.algorithmSuite,
      commitmentPolicy := test.vector.commitmentPolicy,
      encryptedDataKeys := materials.encryptedDataKeys,
      encryptionContext := materials.encryptionContext,
      keyDescription := test.vector.decryptDescription,
      expectedResult := DecryptResult(
        plaintextDataKey := materials.plaintextDataKey,
        // PositiveDecryptKeyringTest only supports automatic creation from a single Encrypt vector
        symmetricSigningKey := if materials.symmetricSigningKeys.Some? && 0 < |materials.symmetricSigningKeys.value| then
          Some(materials.symmetricSigningKeys.value[0]) else None,
        requiredEncryptionContextKeys := materials.requiredEncryptionContextKeys
      ),
      description := if test.vector.description.Some? then
        Some("Decryption for " + test.vector.description.value)
      else None,
      reproducedEncryptionContext := reproducedEncryptionContext
    );

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var maybeKeyring := keys.CreateWappedTestVectorKeyring(
      KeyVectorsTypes.TestVectorKeyringInput(
        keyDescription := vector.keyDescription
      )
    );
    var keyring :- maybeKeyring.MapFailure((e: KeyVectorsTypes.Error) => var _ := printErr(e); "Keyring failure");

    var maybeCmm := mpl
    .CreateDefaultCryptographicMaterialsManager(
      Types.CreateDefaultCryptographicMaterialsManagerInput( keyring := keyring )
    );
    var cmm :- maybeCmm.MapFailure(e => "CMM failure");

    return Success(DecryptTest(
                     input := input,
                     cmm := cmm,
                     vector := vector
                   ));
  }


  // Helper method because debugging can be hard
  function printErr(e: KeyVectorsTypes.Error) : (){()} by method {print e, "\n", "\n"; return ();}
  datatype EncryptTestVector =
    | PositiveEncryptKeyringVector(
        name: string,
        description: Option<string>,
        encryptionContext: Types.EncryptionContext,
        commitmentPolicy: Types.CommitmentPolicy,
        // algorithmSuiteId is NOT an option
        // because test vectors are not the place to test defaults
        algorithmSuite: Types.AlgorithmSuiteInfo,
        maxPlaintextLength: Option<UInt.int64>,
        requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys>,
        encryptDescription: KeyVectorsTypes.KeyDescription,
        decryptDescription: KeyVectorsTypes.KeyDescription
      )
    | NegativeEncryptKeyringVector(
        name: string,
        description: Option<string>,
        encryptionContext: Types.EncryptionContext,
        commitmentPolicy: Types.CommitmentPolicy,
        // algorithmSuiteId is NOT an option
        // because test vectors are not the place to test defaults
        algorithmSuite: Types.AlgorithmSuiteInfo,
        maxPlaintextLength: Option<UInt.int64>,
        requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys>,
        errorDescription: string,
        keyDescription: KeyVectorsTypes.KeyDescription
      )
      // | PositiveEncryptCMMTest
      // | NegativeEncryptCMMTest

  datatype DecryptTestVector =
    | PositiveDecryptKeyringTest(
        name: string,
        algorithmSuite: Types.AlgorithmSuiteInfo,
        commitmentPolicy: Types.CommitmentPolicy,
        encryptedDataKeys: Types.EncryptedDataKeyList,
        encryptionContext: Types.EncryptionContext,
        keyDescription: KeyVectorsTypes.KeyDescription,
        expectedResult: DecryptResult,
        description: Option<string> := None,
        reproducedEncryptionContext: Option<Types.EncryptionContext> := None
      )
    | NegativeDecryptKeyringTest(
        name: string,
        algorithmSuite: Types.AlgorithmSuiteInfo,
        commitmentPolicy: Types.CommitmentPolicy,
        encryptedDataKeys: Types.EncryptedDataKeyList,
        encryptionContext: Types.EncryptionContext,
        errorDescription: string,
        keyDescription: KeyVectorsTypes.KeyDescription,
        reproducedEncryptionContext: Option<Types.EncryptionContext> := None,
        description: Option<string> := None
      )
      // | PositiveDecryptCMMTest
      // | NegativeDecryptCMMTest


  datatype DecryptResult = DecryptResult(
    plaintextDataKey: Option<Types.Secret>,
    symmetricSigningKey: Option<Types.Secret>,
    requiredEncryptionContextKeys: Types.EncryptionContextKeys
    // TODO Add support for the signature key
    // verificationKey: Option<Types.Secret>,
  )

}
