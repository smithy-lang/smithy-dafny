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
        TestGetAggregateKnownValue(client);
    }

    method TestGetAggregate(client: ISimpleAggregateClient)
    requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
      {
        var stringList := ["Test"];
        var simpleStringMap := map["Test1" := "Success"];
        var structureList :=[StructureListElement(stringValue := Some("Test2"), integerValue := Some(2))];
        var simpleIntegerMap := map["Test3" := 3];
        var nestedStructure := NestedStructure(stringStructure := Some(StringStructure(value := Some("Nested"))));
        var ret :- expect client.GetAggregate(GetAggregateInput(simpleIntegerMap := Some(simpleIntegerMap),
                                                                simpleStringMap := Some(simpleStringMap),
                                                                simpleStringList := Some(stringList),
                                                                structureList := Some(structureList),
                                                                nestedStructure := Some(nestedStructure))
                                                                );
        expect ret.simpleStringList.UnwrapOr([]) == stringList;
        expect ret.structureList.UnwrapOr([]) == structureList;
        expect ret.simpleStringMap.UnwrapOr(map[]) == simpleStringMap;
        expect ret.simpleIntegerMap.UnwrapOr(map[]) == simpleIntegerMap;
        expect ret.nestedStructure.UnwrapOr(NestedStructure(stringStructure := Some(StringStructure(value := Some(""))))) == nestedStructure;
        print ret;
    }

    method TestGetAggregateKnownValue(client: ISimpleAggregateClient)
    requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
      {
        var stringList := ["Test"];
        var simpleStringMap := map["Test1" := "Success"];
        var structureList :=[StructureListElement(stringValue := Some("Test2"), integerValue := Some(2))];
        var simpleIntegerMap := map["Test3" := 3];
        var nestedStructure := NestedStructure(stringStructure := Some(StringStructure(value := Some("Nested"))));
        var ret :- expect client.GetAggregate(GetAggregateInput(simpleIntegerMap := Some(simpleIntegerMap),
                                                                simpleStringMap := Some(simpleStringMap),
                                                                simpleStringList := Some(stringList),
                                                                structureList := Some(structureList),
                                                                nestedStructure := Some(nestedStructure))
                                                                );
        expect ret.simpleStringList.UnwrapOr([]) == stringList;
        expect ret.structureList.UnwrapOr([]) == structureList;
        expect ret.simpleStringMap.UnwrapOr(map[]) == simpleStringMap;
        expect ret.simpleIntegerMap.UnwrapOr(map[]) == simpleIntegerMap;
        expect ret.nestedStructure.UnwrapOr(NestedStructure(stringStructure := Some(StringStructure(value := Some(""))))) == nestedStructure;
        print ret;
    }
}