// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "AllAlgorithmSuites.dfy"

module {:options "-functionSyntax:4"} AllMulti {
  import opened Wrappers
  import AllAlgorithmSuites
  import TestVectors
  import KeyVectorsTypes = AwsCryptographyMaterialProvidersTestVectorKeysTypes
  import AllRawAES

  // Let's create some static key descriptions for the Multi Keyring scenario
  // TODO: add more configurations. Right now we just have simple happy path
  const OnlyGeneratorKeyDescriptions :=
    set
      key <- AllRawAES.aesPersistentKeyNames
      ::
        KeyVectorsTypes.Multi(KeyVectorsTypes.MultiKeyring(
                                generator := Some(KeyVectorsTypes.KeyDescription.AES(
                                                    KeyVectorsTypes.RawAES(
                                                      keyId := key,
                                                      providerId := "aws-raw-vectors-persistent-" + key
                                                    ))),
                                childKeyrings := []
                              ))

  const KeyDescriptionsGeneratorAndChildren :=
    set
      key <- AllRawAES.aesPersistentKeyNames
      ::
        KeyVectorsTypes.Multi(KeyVectorsTypes.MultiKeyring(
                                generator := Some(KeyVectorsTypes.KeyDescription.AES(
                                                    KeyVectorsTypes.RawAES(
                                                      keyId := key,
                                                      providerId := "aws-raw-vectors-persistent-" + key
                                                    ))),
                                childKeyrings := getChildKeyrings(AllRawAES.aesPersistentKeyNames, key)
                              ))


  const KeyDescriptions := OnlyGeneratorKeyDescriptions + KeyDescriptionsGeneratorAndChildren

  const Tests: set<TestVectors.EncryptTestVector> :=
    set
      keyDescription <- KeyDescriptions,
      algorithmSuite <- AllAlgorithmSuites.AllAlgorithmSuites,
      commitmentPolicy | commitmentPolicy == AllAlgorithmSuites.GetCompatibleCommitmentPolicy(algorithmSuite)
      ::
        TestVectors.PositiveEncryptKeyringVector(
          name := "MultiKeyring " + keyDescription.Multi.generator.value.AES.keyId,
          encryptionContext := map[],
          commitmentPolicy := commitmentPolicy,
          algorithmSuite := algorithmSuite,
          encryptDescription := keyDescription,
          decryptDescription := keyDescription
        )


  function getChildKeyrings(keys: seq<string>, key: string, i: int := 0) : seq<KeyVectorsTypes.KeyDescription>
    requires 0 <= i <= |keys|
    decreases |keys| - i
  {
    if i == |keys| then
      []
    else
    if keys[i] == key then
      getChildKeyrings(keys, key, i+1)
    else
      [KeyVectorsTypes.KeyDescription.AES(
         KeyVectorsTypes.RawAES(
           keyId := keys[i],
           providerId := "aws-raw-vectors-persistent-" + keys[i]))] + getChildKeyrings(keys, key, i+1)
  }
}
