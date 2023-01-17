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
  simpleStringList: SimpleStringList,
  structureList: StructureList,
  SimpleStringMap: SimpleStringMap,
  SimpleIntegerMap: SimpleIntegerMap,
  very: Deeply,
}

structure GetAggregateOutput {
  simpleStringList: SimpleStringList,
  structureList: StructureList,
  SimpleStringMap: SimpleStringMap,
  SimpleIntegerMap: SimpleIntegerMap,
  very: Deeply,
}

list SimpleStringList {
  member: string
}

list StructureList {
  member: StructureListElement
}

// More elements SHOULD be added
structure StructureListElement {
  s: string,
  i: integer,
}

map SimpleStringMap {
  key: string,
  value: string,
}

// Other map combinations SHOULD be added
map SimpleIntegerMap {
  key: integer,
  value: integer,
}

structure Deeply {
  nested: Nested
}

structure Nested {
  value: string,
}