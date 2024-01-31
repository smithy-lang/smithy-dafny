// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"
include "../../KeyVectors/src/Index.dfy"

module {:options "-functionSyntax:4"} TestVectors {
  import Types = AwsCryptographyMaterialProvidersTypes
  import WrappedMaterialProviders
  import Seq

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
    ensures testResult && !test.vector.NegativeEncryptKeyringVector? ==> materials.Some?
  {
    print "\nTEST===> ",
          test.vector.name,
          if test.vector.description.Some? then "\n" + test.vector.description.value else "",
          if test.vector.NegativeEncryptKeyringVector? then "\n" + test.vector.errorDescription else "", "\n";

    var result := test.cmm.GetEncryptionMaterials(test.input);

    testResult := match test.vector
      case PositiveEncryptKeyringVector(_,_,_,_,_,_,_,_,_,_)
        => result.Success?
      case PositiveEncryptNegativeDecryptKeyringVector(_,_,_,_,_,_,_,_,_,_,_)
        => result.Success?
      case NegativeEncryptKeyringVector(_,_,_,_,_,_,_,_,_)
        => !result.Success?;

    materials := if testResult && result.Success? then
      Some(result.value.encryptionMaterials)
    else
      None;

    if !testResult {
      if test.vector.PositiveEncryptKeyringVector? || test.vector.PositiveEncryptNegativeDecryptKeyringVector? {
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
      case PositiveEncryptKeyringVector(_,_,_,_,_,_,_,_,_,_) =>
        Types.GetEncryptionMaterialsInput(
          encryptionContext := vector.encryptionContext,
          commitmentPolicy := vector.commitmentPolicy,
          algorithmSuiteId := Some(vector.algorithmSuite.id),
          maxPlaintextLength := vector.maxPlaintextLength,
          requiredEncryptionContextKeys := vector.requiredEncryptionContextKeys
        )
      case NegativeEncryptKeyringVector(_,_,_,_,_,_,_,_, _) =>
        Types.GetEncryptionMaterialsInput(
          encryptionContext := vector.encryptionContext,
          commitmentPolicy := vector.commitmentPolicy,
          algorithmSuiteId := Some(vector.algorithmSuite.id),
          maxPlaintextLength := vector.maxPlaintextLength,
          requiredEncryptionContextKeys := vector.requiredEncryptionContextKeys
        )
      case PositiveEncryptNegativeDecryptKeyringVector(_,_,_,_,_,_,_,_,_,_,_) =>
        Types.GetEncryptionMaterialsInput(
          encryptionContext := vector.encryptionContext,
          commitmentPolicy := vector.commitmentPolicy,
          algorithmSuiteId := Some(vector.algorithmSuite.id),
          maxPlaintextLength := vector.maxPlaintextLength,
          requiredEncryptionContextKeys := vector.requiredEncryptionContextKeys
        );


    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var cmm' := keys.CreateWrappedTestVectorCmm(
      KeyVectorsTypes.TestVectorCmmInput(
        keyDescription := if vector.PositiveEncryptKeyringVector? then
          vector.encryptDescription
        else if vector.PositiveEncryptNegativeDecryptKeyringVector? then
          vector.encryptDescription
        else
          vector.keyDescription,
        forOperation := KeyVectorsTypes.ENCRYPT
      ));
    var cmm :- cmm'.MapFailure((e: KeyVectorsTypes.Error) => var _ := printErr(e); "Cmm failure");

    return Success(EncryptTest(
                     input := input,
                     cmm := cmm,
                     vector := vector
                   ));
  }

  function EncryptTestToDecryptVector(test: EncryptTest, materials: Types.EncryptionMaterials)
    : (output: DecryptTestVector)
    requires test.vector.PositiveEncryptKeyringVector? || test.vector.PositiveEncryptNegativeDecryptKeyringVector?
  {
    // It is important to remove these keys
    // since the contract is that they MUST be reproduced!
    var keysToRemove := Seq.ToSet(test.vector.requiredEncryptionContextKeys.UnwrapOr([]));
    match test.vector
    case PositiveEncryptKeyringVector(_, _,_, _, _, _, _,_,_, _) =>
      PositiveDecryptKeyringTest(
        name := test.vector.name + "->Decryption",
        algorithmSuite := test.vector.algorithmSuite,
        commitmentPolicy := test.vector.commitmentPolicy,
        encryptedDataKeys := materials.encryptedDataKeys,
        // The verification key will only exist on the materials.
        // The expectation is that test.vector.encryptionContext.Items <= materials.encryptionContext.Items
        encryptionContext := materials.encryptionContext - keysToRemove,
        keyDescription := test.vector.decryptDescription,
        expectedResult := DecryptResult(
          plaintextDataKey := materials.plaintextDataKey,
          // PositiveDecryptKeyringTest only supports automatic creation from a single Encrypt vector
          symmetricSigningKey := if materials.symmetricSigningKeys.Some? && 0 < |materials.symmetricSigningKeys.value| then
            Some(materials.symmetricSigningKeys.value[0]) else None,
          requiredEncryptionContextKeys := test.vector.requiredEncryptionContextKeys.UnwrapOr([])
        ),
        description := if test.vector.description.Some? then
          Some("Decryption for " + test.vector.description.value)
        else None,
        reproducedEncryptionContext := test.vector.reproducedEncryptionContext
      )
    case PositiveEncryptNegativeDecryptKeyringVector(_, _,_, _, _, _, _,_,_,_, _) =>
      NegativeDecryptKeyringTest(
        name := test.vector.name + "->Decryption",
        algorithmSuite := test.vector.algorithmSuite,
        commitmentPolicy := test.vector.commitmentPolicy,
        encryptedDataKeys := materials.encryptedDataKeys,
        encryptionContext := test.vector.encryptionContext - keysToRemove,
        keyDescription := test.vector.decryptDescription,
        errorDescription := test.vector.decryptErrorDescription,
        description := if test.vector.description.Some? then
          Some("Decryption for " + test.vector.description.value)
        else None,
        reproducedEncryptionContext := test.vector.reproducedEncryptionContext
      )
  }

  method DecryptVectorToDecryptTest(keys: KeyVectors.KeyVectorsClient, vector: DecryptTestVector)
    returns (output: Result<DecryptTest, string>)
    requires keys.ValidState()
    modifies keys.Modifies
    ensures keys.ValidState()
    ensures output.Success? ==>
              && output.value.cmm.ValidState()
              && fresh(output.value.cmm.Modifies)
  {

    var input := Types.DecryptMaterialsInput(
      algorithmSuiteId := vector.algorithmSuite.id,
      commitmentPolicy := vector.commitmentPolicy,
      encryptedDataKeys := vector.encryptedDataKeys,
      encryptionContext := vector.encryptionContext,
      reproducedEncryptionContext := vector.reproducedEncryptionContext
    );

    var mpl :- expect WrappedMaterialProviders.WrappedMaterialProviders();

    var cmm' := keys.CreateWrappedTestVectorCmm(
      KeyVectorsTypes.TestVectorCmmInput(
        keyDescription := vector.keyDescription,
        forOperation := KeyVectorsTypes.DECRYPT
      ));
    var cmm :- cmm'.MapFailure(ErrorToString);

    return Success(DecryptTest(
                     input := input,
                     cmm := cmm,
                     vector := vector
                   ));
  }

  function ErrorToString(e: KeyVectorsTypes.Error): string
  {
    match e
    case KeyVectorException(message) => message
    case AwsCryptographyMaterialProviders(mplError) => (
      match mplError
      case AwsCryptographicMaterialProvidersException(message) => message
      case _ => "Unmapped AwsCryptographyMaterialProviders" )
    case _ => "Unmapped KeyVectorException"
  }

  // Helper method because debugging can be hard
  function printErr(e: KeyVectorsTypes.Error) : (){()} by method {print e, "\n", "\n"; return ();}
  datatype EncryptTestVector =
    | PositiveEncryptKeyringVector(
        name: string,
        description: Option<string> := None,
        encryptionContext: Types.EncryptionContext,
        commitmentPolicy: Types.CommitmentPolicy,
        // algorithmSuiteId is NOT an option
        // because test vectors are not the place to test defaults
        algorithmSuite: Types.AlgorithmSuiteInfo,
        maxPlaintextLength: Option<UInt.int64> := None,
        requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys> := None,
        encryptDescription: KeyVectorsTypes.KeyDescription,
        decryptDescription: KeyVectorsTypes.KeyDescription,
        reproducedEncryptionContext: Option<Types.EncryptionContext> := None
      )
    | PositiveEncryptNegativeDecryptKeyringVector(
        name: string,
        description: Option<string> := None,
        encryptionContext: Types.EncryptionContext,
        commitmentPolicy: Types.CommitmentPolicy,
        // algorithmSuiteId is NOT an option
        // because test vectors are not the place to test defaults
        algorithmSuite: Types.AlgorithmSuiteInfo,
        maxPlaintextLength: Option<UInt.int64> := None,
        requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys> := None,
        decryptErrorDescription: string,
        encryptDescription: KeyVectorsTypes.KeyDescription,
        decryptDescription: KeyVectorsTypes.KeyDescription,
        reproducedEncryptionContext: Option<Types.EncryptionContext> := None
      )
    | NegativeEncryptKeyringVector(
        name: string,
        description: Option<string> := None,
        encryptionContext: Types.EncryptionContext,
        commitmentPolicy: Types.CommitmentPolicy,
        // algorithmSuiteId is NOT an option
        // because test vectors are not the place to test defaults
        algorithmSuite: Types.AlgorithmSuiteInfo,
        maxPlaintextLength: Option<UInt.int64> := None,
        requiredEncryptionContextKeys: Option<Types.EncryptionContextKeys> := None,
        errorDescription: string,
        keyDescription: KeyVectorsTypes.KeyDescription
      )

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


  datatype DecryptResult = DecryptResult(
    plaintextDataKey: Option<Types.Secret>,
    symmetricSigningKey: Option<Types.Secret>,
    requiredEncryptionContextKeys: Types.EncryptionContextKeys
    // TODO Add support for the signature key
    // verificationKey: Option<Types.Secret>,
  )

}
