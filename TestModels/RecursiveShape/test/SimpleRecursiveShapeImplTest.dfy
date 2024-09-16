// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleRecursiveShapeImplTest {
  import SimpleRecursiveShape
  import opened SimpleRecursiveShapeTypes
  import opened Wrappers
  method{:test} GetRecursiveShape(){
    var client :- expect SimpleRecursiveShape.SimpleRecursiveShape();
    TestGetRecursiveShape(client);
  }

  method TestGetRecursiveShape(client: ISimpleRecursiveShapeClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var myDataMap: StructuredDataMap := map[];
    // myDataMap := myDataMap["key1" := StructuredData(content := Some(42))];
    myDataMap := myDataMap["key2" := StructuredData(content := Some(IntegerValue(42)))];
    var recursiveUnion := DataMap(myDataMap);

    var ret :- expect client.GetRecursiveShape(GetRecursiveShapeInput(
                                                 recursiveUnion := Some(recursiveUnion)
                                               ));
    expect ret.recursiveUnion.Some?;
    expect ret.recursiveUnion.value.DataMap?;
    expect ret.recursiveUnion.value.DataMap == myDataMap;

    print ret;
  }

  method TestGetRecursiveShapeKnownValue(client: ISimpleRecursiveShapeClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var myDataMap: StructuredDataMap := map[];
    // myDataMap := myDataMap["key1" := StructuredData(content := Some(42))];
    myDataMap := myDataMap["key2" := StructuredData(content := Some(IntegerValue(42)))];
    var recursiveUnion := DataMap(myDataMap);
    var ret :- expect client.GetRecursiveShape(GetRecursiveShapeInput(recursiveUnion := Some(recursiveUnion)));
    expect ret.recursiveUnion.Some?;
    expect ret.recursiveUnion.value.DataMap?;
    expect ret.recursiveUnion.value.DataMap == myDataMap;
  }
}