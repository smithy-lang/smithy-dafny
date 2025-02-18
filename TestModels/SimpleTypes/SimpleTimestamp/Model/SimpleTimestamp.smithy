// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.timestamp

@aws.polymorph#localService(
  sdkId: "SimpleTimestamp",
  config: SimpleTimestampConfig,
)
service SimpleTypesTimestamp {
  version: "2021-11-01",
  resources: [],
  operations: [ GetTimestamp,  GetTimestampRequired],
  errors: [],
}

structure SimpleTimestampConfig {}

operation GetTimestamp {
  input: GetTimestampInput,
  output: GetTimestampOutput,
}

structure GetTimestampInput {
  value: Timestamp
}

structure GetTimestampOutput {
  value: Timestamp
}

operation GetTimestampRequired {
  input: GetTimestampRequiredInput,
  output: GetTimestampRequiredOutput,
}

structure GetTimestampRequiredInput {
  @required
  value: Timestamp
}

structure GetTimestampRequiredOutput {
  @required
  value: Timestamp
}