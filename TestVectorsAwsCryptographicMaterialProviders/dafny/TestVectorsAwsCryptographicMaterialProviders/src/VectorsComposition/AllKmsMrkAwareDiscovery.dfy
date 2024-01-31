// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"
include "AllKmsMrkAware.dfy"

module {:options "-functionSyntax:4"} AllKmsMrkAwareDiscovery {
  import Types = AwsCryptographyMaterialProvidersTypes
  import opened Wrappers
  import TestVectors
  import AllAlgorithmSuites
  import Seq
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import AllKmsMrkAware

  // These values MUST correspond to the KMS keys
  // At this time, this list is simplistic
  const AwsPartitions := [ "aws" ]
  const AWSAccounts := [ "658956600833" ]
  const AllDiscoveryFilters: set<Option<Types.DiscoveryFilter>> := {
    Some(Types.DiscoveryFilter(
           partition := "aws",
           accountIds := [ "658956600833" ]
         )),
    None
  }

  const KeyDescriptions :=
    set
      filter <- AllDiscoveryFilters
      ::
        KeyVectorsTypes.KmsMrkDiscovery(KeyVectorsTypes.KmsMrkAwareDiscovery(
                                          keyId := "",
                                          defaultMrkRegion := "us-west-2",
                                          awsKmsDiscoveryFilter := filter
                                        ))

  const Tests :=
    set
      encryptDescription <- AllKmsMrkAware.KeyDescriptions,
      decryptDescription <- KeyDescriptions,
      algorithmSuite <- AllAlgorithmSuites.AllAlgorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "Generated Discovery KMS MRK " + encryptDescription.KmsMrk.keyId +
          "->" + if decryptDescription.KmsMrkDiscovery.awsKmsDiscoveryFilter.Some? then
            "Filter " + decryptDescription.KmsMrkDiscovery.awsKmsDiscoveryFilter.value.partition
            + " " + Seq.Flatten(decryptDescription.KmsMrkDiscovery.awsKmsDiscoveryFilter.value.accountIds)
          else
            "No Filter",
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := encryptDescription,
          decryptDescription := decryptDescription
        )
}
