// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.dependencies.lite

use com.amazonaws.kms#TrentService

@aws.polymorph#localService(
  sdkId: "SimpleDependencies",
  config: SimpleDependenciesLiteConfig,
  dependencies: [
    TrentService,
  ]
)
service SimpleDependenciesLite {
  version: "2021-11-01",
  resources: [],
  operations: [
    EncryptWithKMS,
    DecryptWithKMS,
  ],
  errors: [],
}

structure SimpleDependenciesLiteConfig {}

operation EncryptWithKMS {

}

operation DecryptWithKMS {
  
}