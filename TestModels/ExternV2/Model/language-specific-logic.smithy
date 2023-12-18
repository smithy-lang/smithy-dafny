// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.dafnyExternV2

@aws.polymorph#localService(
  sdkId: "LanguageSpecificLogic",
  config: LanguageSpecificLogicConfig,
)
service LanguageSpecificLogic {
  version: "2021-11-01",
  resources: [],
  operations: [ AllRuntimesMethod ],
  errors: [],
}

structure LanguageSpecificLogicConfig {}

// This operation eventualy calls an extern
// This is to test writing/passing externs
// in every runtime.
operation AllRuntimesMethod {
  input: AllRuntimesInput,
  output: AllRuntimesOutput,
}

structure AllRuntimesInput {
  stringValue: String,
}

structure AllRuntimesOutput {
  stringValue: String,
}
