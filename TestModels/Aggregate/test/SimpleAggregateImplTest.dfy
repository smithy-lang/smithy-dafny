// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleAggregateImplTest {
    import SimpleAggregate
    import opened SimpleAggregateTypes
    import opened Wrappers
    method{:test} GetAggregate(){
      var client :- expect SimpleAggregate.SimpleAggregate();
      TestAggregate(client);
    }

    method TestAggregate(client: ISimpleAggregateClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
      TestGetAggregate(client);
      TestGetAggregateKnownValue(client);
      TestEmptyAggregate(client);
      TestNoneAggregate(client);
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

    method TestEmptyAggregate(client: ISimpleAggregateClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
      {
        var stringList := [];
        var simpleStringMap := map[];
        var structureList :=[];
        var simpleIntegerMap := map[];
        var nestedStructure := NestedStructure(stringStructure := Some(StringStructure(value := Some("Nested"))));
        var ret :- expect client.GetAggregate(GetAggregateInput(simpleIntegerMap := Some(simpleIntegerMap),
                                                                simpleStringMap := Some(simpleStringMap),
                                                                simpleStringList := Some(stringList),
                                                                structureList := Some(structureList),
                                                                nestedStructure := Some(nestedStructure))
                                                                );
        expect ret.simpleStringList == Some(stringList);
        expect ret.structureList == Some(structureList);
        expect ret.simpleStringMap == Some(simpleStringMap);
        expect ret.simpleIntegerMap == Some(simpleIntegerMap);
        expect ret.nestedStructure.UnwrapOr(NestedStructure(stringStructure := Some(StringStructure(value := Some(""))))) == nestedStructure;
        print ret;
    }

    method TestNoneAggregate(client: ISimpleAggregateClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
      {

        var ret :- expect client.GetAggregate(
          GetAggregateInput(
            simpleIntegerMap := None,
            simpleStringMap := None,
            simpleStringList := None,
            structureList := None,
            nestedStructure := None)
          );
        expect ret.simpleStringList == None;
        expect ret.structureList == None;
        expect ret.simpleStringMap == None;
        expect ret.simpleIntegerMap == None;
        expect ret.nestedStructure == None;
        print ret;
    }
}