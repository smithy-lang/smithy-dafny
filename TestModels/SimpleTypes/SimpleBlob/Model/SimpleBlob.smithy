// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.blob

@aws.polymorph#localService(
  sdkId: "SimpleBlob",
  config: SimpleBlobConfig,
)
service SimpleTypesBlob {
  version: "2021-11-01",
  resources: [],
  operations: [ GetBlob, GetBlobKnownValueTest ],
  errors: [],
}

structure SimpleBlobConfig {}

operation GetBlob {
  input: GetBlobInput,
  output: GetBlobOutput,
}

operation GetBlobKnownValueTest {
  input: GetBlobInput,
  output: GetBlobOutput,
}

structure GetBlobInput {
  value: Blob
}

structure GetBlobOutput {
  value: Blob
}