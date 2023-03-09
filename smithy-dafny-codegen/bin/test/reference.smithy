// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

namespace aws.polymorph

service AwsMaterialProviders {
    version: "2021-11-01",
    resources: [Keyring],
}

resource Keyring {
    operations: [OnEncrypt]
}

@reference(resource: Keyring)
structure KeyringReference {}

operation OnEncrypt {
    input: OnEncryptInput,

}
structure OnEncryptInput {
    test: KeyringReference
}

@trait(selector: "structure")
structure reference {
  service: String,
  resource: String
}
