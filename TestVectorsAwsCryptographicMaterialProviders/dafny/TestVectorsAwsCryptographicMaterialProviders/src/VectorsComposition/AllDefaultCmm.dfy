// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"
include "AllRawAES.dfy"

module {:options "-functionSyntax:4"} AllDefaultCmm {
  import opened JSON.Values
  import opened Wrappers
  import AllAlgorithmSuites
  import AllRawAES
  import SortedSets
  import StandardLibrary

  import opened UTF8
  import TestVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import Types = AwsCryptographyMaterialProvidersTypes

  const StaticNotPlaintextDataKey
    := KeyVectorsTypes.Static(KeyVectorsTypes.StaticKeyring(
                                keyId := "no-plaintext-data-key"
                              ))

  const StaticPlaintextDataKey
    := KeyVectorsTypes.Static(KeyVectorsTypes.StaticKeyring(
                                keyId := "static-plaintext-data-key"
                              ))

  const StaticAlgorithmSuite := AllAlgorithmSuites.AlgorithmSuites.GetESDKSuite(
                                  AllAlgorithmSuites.Types.ALG_AES_128_GCM_IV12_TAG16_NO_KDF)

  const AesKey := AllRawAES.aesPersistentKeyNames[|AllRawAES.aesPersistentKeyNames| - 1]
  const RawAesKeyring
    := KeyVectorsTypes.AES(KeyVectorsTypes.RawAES(
                             keyId := AesKey,
                             providerId := "aws-raw-vectors-persistent-" + AesKey
                           ))
  function SubSets(ec: map<Types.Utf8Bytes, Types.Utf8Bytes>, keys: seq<Types.Utf8Bytes>)
    : set<map<Types.Utf8Bytes, Types.Utf8Bytes>>
    requires keys == SortedSets.ComputeSetToOrderedSequence2(ec.Keys, (a, b) => a < b)
  {
    if |ec| == 0 then
      {map[]}
    else
      var subsets := SubSets(ec - {keys[0]}, keys[1..]);
      subsets
      + (set
           s <- subsets
           ::
             s + map[keys[0] := ec[keys[0]]])
  }

  const a := UTF8.Encode("a").value
  const b := UTF8.Encode("b").value
  const c := UTF8.Encode("c").value

  // Dafny has trouble with complex operations on maps in Java
  // by decomposing this outside the set comprehension
  // the translated Java compiles correctly
  const rootEncryptionContext := map[a := a, b := b]
  const encryptionContextsToTest := {rootEncryptionContext}
  const disjointEncryptionContext := map[a := c, b := c, c := c]

  lemma disjointEncryptionContextCorrect()
    ensures rootEncryptionContext.Values !! disjointEncryptionContext.Values
    ensures rootEncryptionContext.Items !! disjointEncryptionContext.Items
  {}

  const SuccessTestingRequiredEncryptionContextKeysReproducedEncryptionContext :=
    set
      encryptionContext <- encryptionContextsToTest,
      requiredEncryptionContextKeys
      <- set
           s <- SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s.Keys,
      reproducedEncryptionContext
      <- set
           s <- SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           | s.Keys * requiredEncryptionContextKeys == requiredEncryptionContextKeys
           :: s
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Success testing requiredEncryptionContextKeys/reproducedEncryptionContext",
          commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(StaticAlgorithmSuite),
          algorithmSuite := StaticAlgorithmSuite,
          encryptDescription := RawAesKeyring,
          decryptDescription := RawAesKeyring,
          encryptionContext := encryptionContext,
          requiredEncryptionContextKeys := Some(SortedSets.ComputeSetToSequence(requiredEncryptionContextKeys)),
          reproducedEncryptionContext := Some(reproducedEncryptionContext)
        )

  const FailureBadReproducedEncryptionContext :=
    set
      encryptionContext <- encryptionContextsToTest,
      requiredEncryptionContextKeys
      <- set
           s <- SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s.Keys,
      incorrectEncryptionContext
      <- set
           s <- SubSets(
                  disjointEncryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(disjointEncryptionContext.Keys, (a, b) => a < b))
           | s != map[]
           :: s,
      reproducedEncryptionContext
      <- set
           s <- SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s + incorrectEncryptionContext
      ::
        TestVectors.PositiveEncryptNegativeDecryptKeyringVector(
          name := "Failure of reproducedEncryptionContext",
          decryptErrorDescription := "The reproducedEncryptionContext is not correct",
          commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(StaticAlgorithmSuite),
          algorithmSuite := StaticAlgorithmSuite,
          encryptDescription := RawAesKeyring,
          decryptDescription := RawAesKeyring,
          encryptionContext := encryptionContext,
          requiredEncryptionContextKeys := Some(SortedSets.ComputeSetToSequence(requiredEncryptionContextKeys)),
          reproducedEncryptionContext := Some(reproducedEncryptionContext)
        )

  const Tests
  := {}
  + {
    TestVectors.PositiveEncryptKeyringVector(
      name := "Simplest possible happy path",
      commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(StaticAlgorithmSuite),
      algorithmSuite := StaticAlgorithmSuite,
      encryptDescription := StaticPlaintextDataKey,
      decryptDescription := StaticPlaintextDataKey,
      encryptionContext := map[]
    ),
    TestVectors.NegativeEncryptKeyringVector(
      name := "Missing plaintext data key on decrypt",
      errorDescription := "No plaintext data key on encrypt fails",
      commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(StaticAlgorithmSuite),
      algorithmSuite := StaticAlgorithmSuite,
      keyDescription := StaticNotPlaintextDataKey,
      encryptionContext := map[]

    ),
    TestVectors.PositiveEncryptNegativeDecryptKeyringVector(
      name := "Missing plaintext data key on decrypt",
      decryptErrorDescription := "No plaintext data key on encrypt fails",
      commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(StaticAlgorithmSuite),
      algorithmSuite := StaticAlgorithmSuite,
      encryptDescription := StaticPlaintextDataKey,
      decryptDescription := StaticNotPlaintextDataKey,
      encryptionContext := map[]
    )
  }
  + FailureBadReproducedEncryptionContext
  + SuccessTestingRequiredEncryptionContextKeysReproducedEncryptionContext
}
