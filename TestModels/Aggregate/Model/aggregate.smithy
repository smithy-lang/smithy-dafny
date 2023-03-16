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

map SimpleStructureMap {
  key: String,
  value: Integer,
}

structure NestedStructure {
  stringStructure: StringStructure
}

structure StringStructure {
  value: String,
}

// Aggregates depending on Reference traits are implemented separately from simple aggregates.
// Shapes with a Reference trait depend on the Resources module,
// which may not necessarily be implmented at the same time as Aggregates.

@aws.polymorph#localService(
  sdkId: "SimpleAggregateWithReference",
  config: SimpleAggregateWithReferenceConfig,
)
service SimpleAggregateWithReference {
  version: "2021-11-01",
  resources: [],
  operations: [ GetAggregateWithReferenceTrait ],
  errors: [],
}

structure SimpleAggregateWithReferenceConfig {
    // Structure.Reference
  structureWithReference: StructureWithReference,
  // Map.Values.Reference[]
  mapOfReferences: MapOfReferences,
  // Structure1.Structure2.Reference
  nestedStructureWithReference: NestedStructureWithReference,
  // Map1.Values.Map2.Values.Reference[]
  nestedMapOfReferences: NestedMapOfReferences,
  // Structure.Map.Values.Reference[]
  structureWithMapOfReferences: StructureWithMapOfReferences,
  // Map.Values.Structure[].Reference
  mapOfStructuresWithReference: MapOfStructuresWithReference,
}

// Copied from resources; otherwise this 
@aws.polymorph#reference(resource: ResourceReference)
structure SimpleResourceReference {}

resource ResourceReference {
}

operation GetAggregateWithReferenceTrait {
  input: GetAggregateWithReferenceTraitInput,
  output: GetAggregateWithReferenceTraitOutput,
}

structure GetAggregateWithReferenceTraitInput {
  // Structure.Reference
  structureWithReference: StructureWithReference,
  // Map.Values.Reference[]
  mapOfReferences: MapOfReferences,
  // Structure1.Structure2.Reference
  nestedStructureWithReference: NestedStructureWithReference,
  // Map1.Values.Map2.Values.Reference[]
  nestedMapOfReferences: NestedMapOfReferences,
  // Structure.Map.Values.Reference[]
  structureWithMapOfReferences: StructureWithMapOfReferences,
  // Map.Values.Structure[].Reference
  mapOfStructuresWithReference: MapOfStructuresWithReference,
}

structure GetAggregateWithReferenceTraitOutput {
  // Structure.Reference
  structureWithReference: StructureWithReference,
  // Map.Values.Reference[]
  mapOfReferences: MapOfReferences,
  // Structure1.Structure2.Reference
  nestedStructureWithReference: NestedStructureWithReference,
  // Map1.Values.Map2.Values.Reference[]
  nestedMapOfReferences: NestedMapOfReferences,
  // Structure.Map.Values.Reference[]
  structureWithMapOfReferences: StructureWithMapOfReferences,
  // Map.Values.Structure[].Reference
  mapOfStructuresWithReference: MapOfStructuresWithReference,
}

structure StructureWithReference {
  referenceMember: SimpleResourceReference,
}

map MapOfReferences {
  key: String,
  value: SimpleResourceReference,
}

structure NestedStructureWithReference {
  structureMember: StructureWithReference,
}

map NestedMapOfReferences {
  key: String,
  value: MapOfReferences,
}

structure StructureWithMapOfReferences {
  mapMember: MapOfReferences,
}

map MapOfStructuresWithReference {
  key: String,
  value: StructureWithReference
}