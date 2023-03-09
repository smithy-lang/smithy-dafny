// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

namespace aws.polymorph

service AwsMaterialProviders {
    version: "2021-11-01",
    resources: [Keyring],
    operations: [CreateKeyring]
}

resource Keyring {}

@reference(resource: Keyring)
structure KeyringReference {}

operation CreateKeyring {
    output: CreateKeyringOutput
}

@positional
structure CreateKeyringOutput {
    keyring: KeyringReference
}

@trait(selector: "structure")
structure positional {}

@trait(selector: "structure")
structure reference {
  service: String,
  resource: String
}
