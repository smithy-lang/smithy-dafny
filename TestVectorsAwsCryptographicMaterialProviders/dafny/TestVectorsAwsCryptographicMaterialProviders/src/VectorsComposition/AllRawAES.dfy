// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllRawAES {
  import opened Wrappers
  import TestVectors
  import AllAlgorithmSuites
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  // These are all the PositiveKeyDescription for the RawAESKeyring
  const aesPersistentKeyNames := [ "aes-128", "aes-192", "aes-256"]
  const KeyDescriptions :=
    set
      key <- aesPersistentKeyNames
      ::
        KeyVectorsTypes.AES(KeyVectorsTypes.RawAES(
                              keyId := key,
                              providerId := "aws-raw-vectors-persistent-" + key
                            ))

  const Tests :=
    set
      keyDescription <- KeyDescriptions,
      algorithmSuite <- AllAlgorithmSuites.AllAlgorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Generated RawAES " + keyDescription.AES.keyId,
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := keyDescription,
          decryptDescription := keyDescription
        )
}
