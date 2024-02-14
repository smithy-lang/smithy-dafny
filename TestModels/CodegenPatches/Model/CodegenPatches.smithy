// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.codegenpatches

@aws.polymorph#localService(
  sdkId: "CodegenPatches",
  config: CodegenPatchesConfig
)
service CodegenPatches {
  version: "2021-11-01",
  resources: [],
  operations: [
    GetString,
  ],
}

structure CodegenPatchesConfig {}

operation GetString {
  input: GetStringInput,
  output: GetStringOutput,
}

structure GetStringInput {
  value: String,
}

structure GetStringOutput {
  value: String,
}
