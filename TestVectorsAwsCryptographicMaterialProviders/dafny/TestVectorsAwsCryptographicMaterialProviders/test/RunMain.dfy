// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Test vector projects just run as a CLI
// So all the tests are in the Main.
// By creating a single file here,
// it is easy to kick off a test run.
include "../src/Index.dfy"

module TestWrappedMaterialProvidersMain {
  import WrappedMaterialProvidersMain
  import TestManifests
  import CompleteVectors
  import opened MplManifestOptions

  // This MUST go before TestEncryptManifest
  method {:test} TestGenerateEncryptManifest() {
    var result := CompleteVectors.WriteStuff(
      EncryptManifest(
        encryptManifestOutput := "dafny/TestVectorsAwsCryptographicMaterialProviders/test/"
      ));
    if result.Failure? {
      print result.error;
    }
    expect result.Success?;
  }

  // This MUST go before TestDecryptManifest
  method {:test} TestEncryptManifest() {
    var result := TestManifests.StartEncrypt(
      Encrypt(
        manifestPath := "dafny/TestVectorsAwsCryptographicMaterialProviders/test/",
        decryptManifestOutput := "dafny/TestVectorsAwsCryptographicMaterialProviders/"
      )
    );
    if result.Failure? {
      print result.error;
    }
    expect result.Success?;
  }

  method {:test} TestDecryptManifest() {
    var result := TestManifests.StartDecrypt(
      Decrypt(
        manifestPath := "dafny/TestVectorsAwsCryptographicMaterialProviders/"
      )
    );
    if result.Failure? {
      print result;
    }
    expect result.Success?;
  }

}
