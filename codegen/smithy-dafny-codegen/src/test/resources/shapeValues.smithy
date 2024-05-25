// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
$version: "2.0"

metadata "testCases" = [
  {
    id: "NoParameters"
    shape: aws.polymorph#MyNestedStructure
    value: {}
  },
  {
    id: "StressTest"
    shape: aws.polymorph#MyNestedStructure
    value: {
      myLong: 123456789012345
      myInteger: 42,
      myBlob: "0101",
      myBoolean: false,
      myList: ["1", "2", "3"],
      myNestedList: [
        {
          "a": {
            c: ["b"]
          },
        },
      ]
      myStringMap: {
        "a": "b",
        "c": "d"
      },
      myNestedMap: {
        "a": {},
        "c": {a: 0}
      }
    }
  },
]

namespace aws.polymorph

@aws.polymorph#localService(
  sdkId: "DummyService",
  config: DummyServiceConfig,
) 
service DummyService {}
structure DummyServiceConfig {}

string MyString
integer MyInteger
long MyLong
blob MyBlob
boolean MyBoolean
list MyList {
  member: String
}
list MyNestedList {
  member: MyNestedMap
}
map MyStringMap {
  key: String,
  value: String,
}
map MyNestedMap {
  key: String,
  value: MyStructure,
}
structure MyStructure {
  a: MyInteger
  b: MyString
  c: MyList
}
union MyUnion {
  a: MyInteger
  b: MyString
  c: MyList
}
structure MyNestedStructure {
  myString: MyString
  myInteger: MyInteger
  myLong: MyLong
  myBlob: MyBlob
  myBoolean: MyBoolean
  myList: MyList
  myNestedList: MyNestedList
  myStringMap: MyStringMap
  myNestedMap: MyNestedMap
}

resource MyResource {}

@aws.polymorph#reference(resource: MyResource)
structure MyResourceReference {}
