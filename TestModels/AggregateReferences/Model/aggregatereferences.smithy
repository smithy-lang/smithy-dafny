// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
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
// Shape transitions between structures, unions, maps, and lists,
// plus each being required/not required, are in scope.

// Shapes actually under test:
// config.Union.Structure
// config.Union.Map
// config.Structure.Union
// config.Structure.List
// config.Map.Union
// config.Map.List
// config.List.Structure
// config.List.Map

// This isn't a fixed list and can be added/removed to to test different generations
// Some suggested alternative shapes are commented out
// Dafny verification times out if too many shapes are added
structure SimpleAggregateReferencesConfig {
  // unionWithUnionWithReference: UnionWithUnionWithReference,
  @required
  unionWithStructureWithReference: UnionWithStructureWithReference,
  unionWithMapOfReferences: UnionWithMapOfReferences,
  // unionWithListOfReferences: UnionWithListOfReferences,
  structureWithUnionWithReference: StructureWithUnionWithReference,
  // structureWithStructureWithReference: StructureWithStructureWithReference,
  // structureWithMapOfReferences: StructureWithMapOfReferences,
  @required
  structureWithListOfReferences: StructureWithListOfReferences,
  @required
  mapOfUnionWithReference: MapOfUnionWithReference,
  // mapOfStructureWithReference: MapOfStructureWithReference,
  // mapOfMapOfReferences: MapOfMapOfReferences,
  mapOfListOfReferences: MapOfListOfReferences,
  // listOfUnionWithReference: ListOfUnionWithReference,
  @required
  listOfStructureWithReference: ListOfStructureWithReference,
  listOfMapOfReferences: ListOfMapOfReferences,
  // listOfListOfReferences: ListOfListOfReferences,
}

resource ResourceReference {
}

@aws.polymorph#reference(resource: ResourceReference)
structure ResourceReferenceStructure {}

// Single-wrapped references
union UnionWithReference {
  referenceMember: ResourceReferenceStructure
}

structure StructureWithReference {
  referenceMember: ResourceReferenceStructure
}

map MapOfReferences {
  key: String,
  value: ResourceReferenceStructure
}

list ListOfReferences {
  member: ResourceReferenceStructure
}

// Double-wrapped references

union UnionWithUnionWithReference {
  unionMember: UnionWithReference
}

union UnionWithStructureWithReference {
  structureMember: StructureWithReference
}

union UnionWithMapOfReferences {
  mapMember: MapOfReferences
}

union UnionWithListOfReferences {
  listMember: ListOfReferences
}

structure StructureWithUnionWithReference {
  unionMember: UnionWithReference
}

structure StructureWithStructureWithReference {
  structureMember: StructureWithReference
}

structure StructureWithMapOfReferences {
  mapMember: MapOfReferences
}

structure StructureWithListOfReferences {
  listMember: ListOfReferences
}

map MapOfUnionWithReference {
  key: String,
  value: UnionWithReference
}

map MapOfStructureWithReference {
  key: String,
  value: StructureWithReference
}

map MapOfMapOfReferences {
  key: String,
  value: MapOfReferences
}

map MapOfListOfReferences {
  key: String,
  value: ListOfReferences
}

list ListOfUnionWithReference {
  member: UnionWithReference
}

list ListOfStructureWithReference {
  member: StructureWithReference
}

list ListOfMapOfReferences {
  member: MapOfReferences
}

list ListOfListOfReferences {
  member: ListOfReferences
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
