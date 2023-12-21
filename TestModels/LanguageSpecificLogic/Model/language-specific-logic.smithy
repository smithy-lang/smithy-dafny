// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace language.specific.logic

@aws.polymorph#localService(
  sdkId: "LanguageSpecificLogic",
  config: LanguageSpecificLogicConfig,
)
service LanguageSpecificLogic {
  version: "2021-11-01",
  resources: [],
  operations: [ GetRuntimeInformation ],
  errors: [],
}

structure LanguageSpecificLogicConfig {}

operation GetRuntimeInformation {
  input: Unit,
  output: GetRuntimeInformationOutput,
}

structure GetRuntimeInformationOutput {
  @required
  language: String,
  @required
  runtime: String,
}
