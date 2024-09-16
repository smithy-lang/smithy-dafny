// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleAggregateImplTest {
    import SimpleAggregate
    import opened SimpleAggregateTypes
    import opened Wrappers
    method{:test} GetAggregate(){
        var client :- expect SimpleAggregate.SimpleAggregate();
        TestGetAggregate(client);
    }

    method TestGetAggregate(client: ISimpleAggregateClient)
    requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
      {
        var myDataMap: StructuredDataMap := map[];
        // myDataMap := myDataMap["key1" := StructuredData(content := Some(42))];
        myDataMap := myDataMap["key2" := StructuredData(content := Some(IntegerValue(42)))];
        var myList: ListWithRecursion := [myDataMap];
        var recursiveUnion := ListValue(myList);

        var ret :- expect client.GetAggregate(GetAggregateInput(
                                                                recursiveUnion := Some(recursiveUnion)
                                                                ));
        expect ret.recursiveUnion.Some?;
        expect ret.recursiveUnion.value.ListValue?;
        expect ret.recursiveUnion.value.ListValue == myList;

        print ret;
    }
}