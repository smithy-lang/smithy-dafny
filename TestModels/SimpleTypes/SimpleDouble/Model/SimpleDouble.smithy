// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.types.smithyDouble

@aws.polymorph#localService(
  sdkId: "SimpleDouble",
  config: SimpleDoubleConfig,
)
service SimpleTypesDouble {
  version: "2021-11-01",
  resources: [],
  operations: [ GetDouble ],
  errors: [],
}

structure SimpleDoubleConfig {}

// TODO: https://github.com/awslabs/polymorph/issues/123
// Once we have proper Double serialization,
// we should add a GetDoubleKnownValueTest

operation GetDouble {
  input: GetDoubleInput,
  output: GetDoubleOutput,
}

structure GetDoubleInput {
  value: Double
}

structure GetDoubleOutput {
  value: Double
}
