// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllKmsRsa {
  import ComAmazonawsKmsTypes
  import opened Wrappers
  import TestVectors
  import AllAlgorithmSuites
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  const AllKmsRsaKeys := [ "us-west-2-rsa-mrk" ]

  const KeyDescriptions :=
    set
      key <- AllKmsRsaKeys,
      encryptionAlgorithm <- (set e: ComAmazonawsKmsTypes.EncryptionAlgorithmSpec | !e.SYMMETRIC_DEFAULT?)
      ::
        KeyVectorsTypes.KmsRsa(KeyVectorsTypes.KmsRsaKeyring(
                                 keyId := key,
                                 encryptionAlgorithm := encryptionAlgorithm
                               ))
  // AwsKmsRsaKeyring cannot be used with an Algorithm Suite with asymmetric signing
  const algorithmSuites := set suite <- AllAlgorithmSuites.AllAlgorithmSuites
                               | !suite.signature.ECDSA? :: suite

  const Tests :=
    set
      keyDescription <- KeyDescriptions,
      algorithmSuite <- algorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Generated KMS RSA " + keyDescription.KmsRsa.keyId,
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := keyDescription,
          decryptDescription := keyDescription
        )
}
