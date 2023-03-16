namespace simple.resources

@aws.polymorph#localService(
  sdkId: "SimpleResources",
  config: SimpleResourcesConfig,
)
service SimpleResources {
  version: "2021-11-01",
  resources: [],
  operations: [ GetResources ],
  errors: [ SimpleResourcesException ],
}

structure SimpleResourcesConfig {
  @required @length(min: 1) name: String,
  mapOfReferenceStructures: MapOfSimpleResourceReferenceMemberShapes,
  structureOfMap: StructureOfMap
}

structure TestSimpleResourcesChainConfig {
  @required @length(min: 1) name: String
}

// This operation MUST
// return the values given in the Resources.
// The internal config MUST somehow differ,
// and this additional information MUST be returned.
operation GetResources {
  input: GetResourcesInput,
  output: GetResourcesOutput,
}

structure GetResourcesInput {
  value: String
}

structure GetResourcesOutput {
  @required
  output: SimpleResourceReference
}

@aws.polymorph#reference(resource: SimpleResource)
structure SimpleResourceReference {}

resource SimpleResource {
  operations: [ GetResourceData ]
}

// list ListOfSimpleResourceReferenceMemberShapes {
//   member: SimpleResourceReference
// }

// java.lang.UnsupportedOperationException: Shape simple.resources#SetOfSimpleResourceReferenceMemberShapes has unsupported type set
// set SetOfSimpleResourceReferenceMemberShapes {
//   member: SimpleResourceReference
// }

map MapOfSimpleResourceReferenceMemberShapes {
  key: String,
  value: SimpleResourceReference
}

structure StructureOfMap {
  mapValue: MapOfSimpleResourceReferenceMemberShapes,
}

operation CollectionsOfMemberShapes {
  input: CollectionsOfMemberShapesInput,
  output: CollectionsOfMemberShapesOutput,
}

structure CollectionsOfMemberShapesInput {
  // listOfMembers: ListOfSimpleResourceReferenceMemberShapes,
  // setOfMembers: SetOfSimpleResourceReferenceMemberShapes,
  mapOfReferenceStructures: MapOfSimpleResourceReferenceMemberShapes,
  structureOfMap: StructureOfMap
}

structure CollectionsOfMemberShapesOutput {
  // listOfMembers: ListOfSimpleResourceReferenceMemberShapes,
  // setOfMembers: SetOfSimpleResourceReferenceMemberShapes,
  mapOfReferenceStructures: MapOfSimpleResourceReferenceMemberShapes,
  structureOfMap: StructureOfMap
}

// list ListOfLists {
//   member: ListOfSimpleResourceReferenceMemberShapes
// }

// list ListOfSets {
//   member: SetOfSimpleResourceReferenceMemberShapes
// }

// list ListOfMaps {
//   member: MapOfSimpleResourceReferenceMemberShapes
// }

// map MapOfLists {
//   key: String,
//   value: ListOfSimpleResourceReferenceMemberShapes
// }

// map MapOfSets {
//   key: String,
//   value: SetOfSimpleResourceReferenceMemberShapes
// }

// map MapOfMaps {
//   key: String,
//   value: MapOfSimpleResourceReferenceMemberShapes
// }

operation GetResourceData {
  input: GetResourceDataInput,
  output: GetResourceDataOutput,
}

structure GetResourceDataInput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
//  byteValue: Byte,
//  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
//  floatValue: Float,
//  doubleValue: Double,
//  bigIntegerValue: BigInteger,
//  bigDecimalValue: BigDecimal,
//  timestampValue: Timestamp,
}

structure GetResourceDataOutput {
  blobValue: Blob,
  booleanValue: Boolean,
  stringValue: String,
//  byteValue: Byte,
//  shortValue: Short,
  integerValue: Integer,
  longValue: Long,
//  floatValue: Float,
//  doubleValue: Double,
//  bigIntegerValue: BigInteger,
//  bigDecimalValue: BigDecimal,
//  timestampValue: Timestamp,
}

@error("client")
structure SimpleResourcesException {
  @required
  message: String,
}

