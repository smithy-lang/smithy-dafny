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
  operations: [ GetString, GetStringKnownValue, GetStringUTF8, GetStringUTF8KnownValue ],
  errors: [],
}

structure SimpleStringConfig {}

operation GetString {
  input: GetStringInput,
  output: GetStringOutput,
}

operation GetStringKnownValue {
  input: GetStringInput,
  output: GetStringOutput,
}

operation GetStringUTF8 {
  input: GetStringUTF8Input,
  output: GetStringUTF8Output,
}

operation GetStringUTF8KnownValue {
  input: GetStringUTF8Input,
  output: GetStringUTF8Output,
}

structure GetStringInput {
  value: String
}

structure GetStringOutput {
  value: String
}

@aws.polymorph#dafnyUtf8Bytes
string UTF8Bytes

structure GetStringUTF8Input {
  value: UTF8Bytes
}

structure GetStringUTF8Output {
  value: UTF8Bytes
}