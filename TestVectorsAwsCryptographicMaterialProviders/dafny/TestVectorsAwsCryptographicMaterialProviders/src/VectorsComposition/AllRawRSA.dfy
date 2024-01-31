// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllRawRSA {
  import Types = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import AllAlgorithmSuites
  import TestVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  // These are all the PositiveKeyDescription for the RawRSAKeyring
  const rsaPersistentKeyNamesWithoutPublicPrivate := [ "rsa-4096" ]
  const KeyDescriptions :=
    set
      key <- rsaPersistentKeyNamesWithoutPublicPrivate,
             padding: Types.PaddingScheme
      ::
        KeyVectorsTypes.RSA(KeyVectorsTypes.RawRSA(
                              keyId := key,
                              providerId := "aws-raw-vectors-persistent-" + key,
                              padding := padding
                            ))

  const Tests :=
    set
      keyDescription <- KeyDescriptions,
      algorithmSuite <- AllAlgorithmSuites.AllAlgorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Generated RawRSA " + keyDescription.RSA.keyId,
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := keyDescription.( RSA := keyDescription.RSA.( keyId := keyDescription.RSA.keyId + "-public" ) ),
          decryptDescription := keyDescription.( RSA := keyDescription.RSA.( keyId := keyDescription.RSA.keyId + "-private" ) )
        )
}
