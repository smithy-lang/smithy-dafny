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
  operations: [ GetAggregate, GetAggregateKnownValueTest ],
  errors: [],
}

structure SimpleAggregateConfig {}

operation GetAggregate {
  input: GetAggregateInput,
  output: GetAggregateOutput,
}

operation GetAggregateKnownValueTest {
  input: GetAggregateInput,
  output: GetAggregateOutput,
}

structure GetAggregateInput {
  simpleStringList: SimpleStringList,
  structureList: StructureList,
  simpleStringMap: SimpleStringMap,
  simpleIntegerMap: SimpleIntegerMap,
  nestedStructure: NestedStructure,
}

structure GetAggregateOutput {
  simpleStringList: SimpleStringList,
  structureList: StructureList,
  simpleStringMap: SimpleStringMap,
  simpleIntegerMap: SimpleIntegerMap,
  nestedStructure: NestedStructure,
}

list SimpleStringList {
  member: String
}

list StructureList {
  member: StructureListElement
}

// More elements SHOULD be added
structure StructureListElement {
  stringValue: String,
  integerValue: Integer,
}

map SimpleStringMap {
  key: String,
  value: String,
}

// Other map combinations SHOULD be added
map SimpleIntegerMap {
  key: String,
  value: Integer,
}

structure NestedStructure {
  stringStructure: StringStructure
}

structure StringStructure {
  value: String,
}