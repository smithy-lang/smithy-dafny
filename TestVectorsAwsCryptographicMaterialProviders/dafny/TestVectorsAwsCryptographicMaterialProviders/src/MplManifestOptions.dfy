// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "LibraryIndex.dfy"

module {:options "-functionSyntax:4"} MplManifestOptions {
  import opened Wrappers

  datatype ManifestOptions =
    | Decrypt(
        nameonly manifestPath: string,
        nameonly testName: Option<string> := None
      )
    | Encrypt(
        nameonly manifestPath: string,
        nameonly decryptManifestOutput: string,
        nameonly testName: Option<string> := None
      )
    | EncryptManifest(
        nameonly encryptManifestOutput: string
      )

}
