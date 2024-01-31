// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllKmsMrkAware {
  import opened Wrappers
  import AllAlgorithmSuites
  import TestVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes

  const AllAwsKMSMrkKeys := [ "us-west-2-mrk", "us-east-1-mrk" ]

  const KeyDescriptions :=
    set
      key <- AllAwsKMSMrkKeys
      ::
        KeyVectorsTypes.KmsMrk(KeyVectorsTypes.KmsMrkAware( keyId := key ))

  const Tests :=
    set
      encryptDescription <- KeyDescriptions,
      decryptDescription <- KeyDescriptions,
      algorithmSuite <- AllAlgorithmSuites.AllAlgorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Generated KMS MRK " + encryptDescription.KmsMrk.keyId + "->" + decryptDescription.KmsMrk.keyId,
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := encryptDescription,
          decryptDescription := decryptDescription
        )
}
