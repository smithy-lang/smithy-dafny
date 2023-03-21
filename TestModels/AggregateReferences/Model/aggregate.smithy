namespace simple.aggregate.references

@aws.polymorph#localService(
  sdkId: "SimpleAggregateReferences",
  config: SimpleAggregateReferencesConfig,
)
service SimpleAggregateReferences {
  version: "2021-11-01",
  resources: [],
  operations: [],
  errors: [],
}
// Shape transitions that may be tested:
// Map to Map
// Map to Structure
// Structure to Map
// Structure to Structure
// This, plus each being required/not required.

// Shapes actually under test
// config.Map.Map
// config.Map.Structure.Map
// config.Structure.Map.Structure
// config.Structure.Structure
// config.List.List
// config.List.Map.List
// config.Structure.List.Structure
// This isn't a fixed list and can be added/removed to to test different generations
// Dafny verification times out if too many shapes are added
structure SimpleAggregateReferencesConfig {
  // config.Map.Values.Structure[].Map.Values.Reference[]
  mapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  @required
  requiredMapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  // config.Structure.Map.Values.Structure[].Reference
  structureWithMapOfStructures: StructureWithMapOfStructures,
  @required
  requiredStructureWithMapOfStructures: StructureWithMapOfStructures,
  // config.Structure.Structure.Reference
  nestedStructureWithReference: NestedStructureWithReference,
  // config.Map1.Values.Map2.Values.Reference[]
  nestedMapOfReferences: NestedMapOfReferences,
  // config.List.List[].Reference[]
  nestedList: NestedList,
  // config.List.Map.Values.List[].Reference[]
  @required
  listOfMapOfLists: ListOfMapOfLists,
  // config.Structure.List.Structure[].Reference
  structureWithListOfStructures: StructureWithListOfStructures,
}

structure StructureWithListOfStructures {
  listMember: ListOfStructures
}

list ListOfStructures {
  member: StructureWithReference
}

list ListOfMapOfLists {
  member: MapOfLists
}

map MapOfLists {
  key: String,
  value: ListOfReferences
}

@aws.polymorph#reference(resource: ResourceReference)
structure ResourceReferenceStructure {}

resource ResourceReference {
}

@aws.polymorph#reference(service: ServiceReference)
structure ServiceReferenceStructure {}

resource ServiceReference {
}

list NestedList {
  member: ListOfReferences
}

list ListOfReferences {
  member: ResourceReferenceStructure
}

structure StructureWithMapOfStructures {
  mapMember: MapOfStructuresWithReference
}

map MapOfStructuresOfMapsOfReferences {
  key: String,
  value: StructureWithMapOfReferences
}

map MapOfNestedStructures {
  key: String,
  value: NestedStructureWithReference
}

structure StructureWithReference {
  referenceMember: ResourceReferenceStructure,
}

map MapOfReferences {
  key: String,
  value: ResourceReferenceStructure,
}

structure NestedStructureWithReference {
  structureMember: StructureWithReference,
}

map NestedMapOfReferences {
  key: String,
  value: DoubleNestedMapOfReferences,
}

map DoubleNestedMapOfReferences {
  key: String,
  value: MapOfReferences,
}

structure StructureWithMapOfReferences {
  mapMember: MapOfReferences,
}

structure StructureWithRequiredMapOfReferences {
  @required
  mapMember: MapOfReferences,
}

map MapOfStructuresWithReference {
  key: String,
  value: StructureWithReference
}

// Operations not supported

// operation GetAggregateWithReferenceTrait {
//   input: GetAggregateWithReferenceTraitInput,
//   output: GetAggregateWithReferenceTraitOutput,
// }

// structure GetAggregateWithReferenceTraitInput {
  // // config.Map.Values.Structure[].Map.Values.Reference[]
  // mapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  // @required
  // requiredMapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  // // config.Structure.Map.Values.Structure[].Reference
  // structureWithMapOfStructures: StructureWithMapOfStructures,
  // @required
  // requiredStructureWithMapOfStructures: StructureWithMapOfStructures,
  // // config.Structure.Structure.Reference
  // nestedStructureWithReference: NestedStructureWithReference,
  // // config.Map1.Values.Map2.Values.Reference[]
  // nestedMapOfReferences: NestedMapOfReferences,
  // // config.List.List[].Reference[]
  // nestedList: NestedList,
  // // config.List.Map.Values.List[].Reference[]
  // @required
  // listOfMapOfLists: ListOfMapOfLists,
  // // config.Structure.List.Structure[].Reference
  // structureWithListOfStructures: StructureWithListOfStructures,
// }

// structure GetAggregateWithReferenceTraitOutput {
  // // config.Map.Values.Structure[].Map.Values.Reference[]
  // mapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  // @required
  // requiredMapOfStructuresOfMapsOfReferences: MapOfStructuresOfMapsOfReferences,
  // // config.Structure.Map.Values.Structure[].Reference
  // structureWithMapOfStructures: StructureWithMapOfStructures,
  // @required
  // requiredStructureWithMapOfStructures: StructureWithMapOfStructures,
  // // config.Structure.Structure.Reference
  // nestedStructureWithReference: NestedStructureWithReference,
  // // config.Map1.Values.Map2.Values.Reference[]
  // nestedMapOfReferences: NestedMapOfReferences,
  // // config.List.List[].Reference[]
  // nestedList: NestedList,
  // // config.List.Map.Values.List[].Reference[]
  // @required
  // listOfMapOfLists: ListOfMapOfLists,
  // // config.Structure.List.Structure[].Reference
  // structureWithListOfStructures: StructureWithListOfStructures,
// }
