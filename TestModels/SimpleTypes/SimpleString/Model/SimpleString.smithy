// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.smithyString

@aws.polymorph#localService(
  sdkId: "SimpleString",
  config: SimpleStringConfig,
)
service SimpleTypesString {
  version: "2021-11-01",
  resources: [],
  operations: [ GetString, GetStringSingleValue, GetStringUTF8 ],
  errors: [],
}

structure SimpleStringConfig {}

operation GetString {
  input: GetStringInput,
  output: GetStringOutput,
}

operation GetStringSingleValue {
  input: GetStringInput,
  output: GetStringOutput,
}

operation GetStringUTF8 {
  input: GetStringInput,
  output: GetStringOutput,
}

structure GetStringInput {
  value: String
}

structure GetStringOutput {
  value: String
}
