namespace simple.constraints

@aws.polymorph#localService(
  sdkId: "SimpleConstraints",
  config: SimpleConstraintsConfig,
)
service SimpleConstraints {
  version: "2021-11-01",
  resources: [],
  operations: [ GetConstraints ],
  errors: [ SimpleConstraintsException ],
}

structure SimpleConstraintsConfig {}

operation GetConstraints {
  input: GetConstraintsInput,
  output: GetConstraintsOutput,
}

// See https://smithy.io/2.0/spec/constraint-traits.html

// These constraints will result
// a predicate that will define
// validitaty for a sub set type.
// The predicate can be tested.

@length(min: 1, max: 10)
string MyString

@length(min: 1)
string NonEmptyString

@length(max: 10)
string StringLessThanOrEqualToTen

@length(min: 1, max: 10)
blob MyBlob

@length(min: 1)
blob NonEmptyBlob

@length(max: 10)
blob BlobLessThanOrEqualToTen

@length(min: 1, max: 10)
list MyList {
  member: String
}

@length(min: 1)
list NonEmptyList {
  member: String
}

@length(max: 10)
list ListLessThanOrEqualToTen {
  member: String
}

@length(min: 1, max: 10)
map MyMap {
  key: String,
  value: String,
}

@length(min: 1)
map NonEmptyMap {
  key: String,
  value: String,
}

@length(max: 10)
map MapLessThanOrEqualToTen {
  key: String,
  value: String,
}

@pattern("^[A-Za-z]+$")
string Alphabetic

@range(min: 1, max: 10)
integer OneToTen

@range(min: 1)
integer GreaterThanOne

@range(max: 10)
integer LessThanTen

@uniqueItems
list MyUniqueList {
  member: String
}

@uniqueItems
list MyComplexUniqueList {
  member: ComplexListElement
}

structure ComplexListElement {
  value: String,
  blob: Blob,
}

structure GetConstraintsInput {
  MyString: MyString,
  NonEmptyString: NonEmptyString,
  StringLessThanOrEqualToTen: StringLessThanOrEqualToTen,
  MyBlob: MyBlob,
  NonEmptyBlob: NonEmptyBlob,
  BlobLessThanOrEqualToTen: BlobLessThanOrEqualToTen,
  MyList: MyList,
  NonEmptyList: NonEmptyList,
  ListLessThanOrEqualToTen: ListLessThanOrEqualToTen,
  MyMap: MyMap,
  NonEmptyMap: NonEmptyMap,
  MapLessThanOrEqualToTen: MapLessThanOrEqualToTen,
  Alphabetic: Alphabetic,
  OneToTen: OneToTen,
  GreaterThanOne: GreaterThanOne,
  LessThanTen: LessThanTen,
  MyUniqueList: MyUniqueList,
  MyComplexUniqueList: MyComplexUniqueList,
  MyUtf8Bytes: Utf8Bytes,
  MyListOfUtf8Bytes: ListOfUtf8Bytes,
}

structure GetConstraintsOutput {
  MyString: MyString,
  NonEmptyString: NonEmptyString,
  StringLessThanOrEqualToTen: StringLessThanOrEqualToTen,
  MyBlob: MyBlob,
  NonEmptyBlob: NonEmptyBlob,
  BlobLessThanOrEqualToTen: BlobLessThanOrEqualToTen,
  MyList: MyList,
  NonEmptyList: NonEmptyList,
  ListLessThanOrEqualToTen: ListLessThanOrEqualToTen,
  MyMap: MyMap,
  NonEmptyMap: NonEmptyMap,
  MapLessThanOrEqualToTen: MapLessThanOrEqualToTen,
  Alphabetic: Alphabetic,
  OneToTen: OneToTen,
  GreaterThanOne: GreaterThanOne,
  LessThanTen: LessThanTen,
  MyUniqueList: MyUniqueList,
  MyComplexUniqueList: MyComplexUniqueList,
  MyUtf8Bytes: Utf8Bytes,
  MyListOfUtf8Bytes: ListOfUtf8Bytes,
}

// See Comment in traits.smithy
@aws.polymorph#dafnyUtf8Bytes
string Utf8Bytes

list ListOfUtf8Bytes {
  member: Utf8Bytes
}

@error("client")
structure SimpleConstraintsException {
  @required
  message: String,
}
