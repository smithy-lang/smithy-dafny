// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
namespace simple.aggregate

@aws.polymorph#localService(
  sdkId: "SimpleAggregate",
  config: SimpleAggregateConfig,
)
service SimpleAggregate {
  version: "2021-11-01",
  resources: [],
  operations: [ GetAggregate ],
  errors: [],
}

structure SimpleAggregateConfig {}

operation GetAggregate {
  input: GetAggregateInput,
  output: GetAggregateOutput,
}

structure GetAggregateInput {
  recursiveUnion: RecursiveUnion
}

structure GetAggregateOutput {
  recursiveUnion: RecursiveUnion
}

union RecursiveUnion {
  IntegerValue: Integer,
  StringValue: String,
  ListValue: ListWithRecursion
}

list ListWithRecursion {
  member: StructuredDataMap
}

map StructuredDataMap {
    key: String,
    value: StructuredData
}

structure StructuredData {
    content: RecursiveUnion
}