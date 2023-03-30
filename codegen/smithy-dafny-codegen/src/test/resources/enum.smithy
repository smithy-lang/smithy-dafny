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

operation OnEncrypt {
    input: OnEncryptInput,

}
structure OnEncryptInput {
    test: AlgorithmSuite
}

@enum([
    {
        name: "ALG_AES_128_GCM_IV12_TAG16_NO_KDF",
        value: "0x0014",
    },
    {
        name: "ALG_AES_192_GCM_IV12_TAG16_NO_KDF",
        value: "0x0046",
    },
])
string AlgorithmSuite
