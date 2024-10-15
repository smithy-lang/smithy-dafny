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
    var myDataMap: MapWithRecursion := map["key2" := StructureWithRecursion(content := Some(IntegerValue(42)))];
    var myList: ListWithRecursion := [myDataMap];
    var recursiveUnion := ListValue(myList);

    var ret :- expect client.GetRecursiveShape(GetRecursiveShapeInput(
                                                 recursiveUnion := Some(recursiveUnion)
                                               ));
    expect ret.recursiveUnion.Some?;
    expect ret.recursiveUnion.value.ListValue?;
    expect ret.recursiveUnion.value.ListValue == myList;
  }
}