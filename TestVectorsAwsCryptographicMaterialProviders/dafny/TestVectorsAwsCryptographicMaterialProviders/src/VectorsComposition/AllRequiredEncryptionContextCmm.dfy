// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllRequiredEncryptionContextCmm {
  import opened Wrappers
  import AllAlgorithmSuites
  import SortedSets
  import StandardLibrary
  import TestVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import Types = AwsCryptographyMaterialProvidersTypes
  import AllDefaultCmm

  import opened UTF8

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
           s <- AllDefaultCmm.SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s.Keys,
      reproducedEncryptionContext
      <- set
           s <- AllDefaultCmm.SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           | s.Keys * requiredEncryptionContextKeys == requiredEncryptionContextKeys
           :: s
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Success testing requiredEncryptionContextKeys/reproducedEncryptionContext",
          commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(AllDefaultCmm.StaticAlgorithmSuite),
          algorithmSuite := AllDefaultCmm.StaticAlgorithmSuite,
          encryptDescription := AllDefaultCmm.RawAesKeyring,
          decryptDescription := AllDefaultCmm.RawAesKeyring,
          encryptionContext := encryptionContext,
          requiredEncryptionContextKeys := Some(SortedSets.ComputeSetToSequence(requiredEncryptionContextKeys)),
          reproducedEncryptionContext := Some(reproducedEncryptionContext)
        )

  const FailureBadReproducedEncryptionContext :=
    set
      encryptionContext <- encryptionContextsToTest,
      requiredEncryptionContextKeys
      <- set
           s <- AllDefaultCmm.SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s.Keys,
      incorrectEncryptionContext
      <- set
           s <- AllDefaultCmm.SubSets(
                  disjointEncryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(disjointEncryptionContext.Keys, (a, b) => a < b))
           | s != map[]
           :: s,
      reproducedEncryptionContext
      <- set
           s <- AllDefaultCmm.SubSets(
                  encryptionContext,
                  SortedSets.ComputeSetToOrderedSequence2(encryptionContext.Keys, (a, b) => a < b))
           :: s + incorrectEncryptionContext
      ::
        TestVectors.PositiveEncryptNegativeDecryptKeyringVector(
          name := "Failure of reproducedEncryptionContext",
          decryptErrorDescription := "The reproducedEncryptionContext is not correct",
          commitmentPolicy := AllAlgorithmSuites.GetCompatibleCommitmentPolicy(AllDefaultCmm.StaticAlgorithmSuite),
          algorithmSuite := AllDefaultCmm.StaticAlgorithmSuite,
          encryptDescription := AllDefaultCmm.RawAesKeyring,
          decryptDescription := AllDefaultCmm.RawAesKeyring,
          encryptionContext := encryptionContext,
          requiredEncryptionContextKeys := Some(SortedSets.ComputeSetToSequence(requiredEncryptionContextKeys)),
          reproducedEncryptionContext := Some(reproducedEncryptionContext)
        )
  // These are only required encryption context vectors with static aes keyrings
  const Tests: set<TestVectors.EncryptTestVector> :=
    SuccessTestingRequiredEncryptionContextKeysReproducedEncryptionContext +
    FailureBadReproducedEncryptionContext

}
