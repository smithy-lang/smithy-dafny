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
        var stringList := ["Test"];
        var simpleStringMap := map["Test1" := "Success"];
        var structureList :=[StructureListElement(s := Some("Test2"), i := Some(2))];
        var simpleIntegerMap := map["Test3" := 3];
        var nested := Deeply(nested := Some(Nested(value := Some("Nest"))));
        var ret := client.GetAggregate(GetAggregateInput(SimpleIntegerMap := Some(simpleIntegerMap), SimpleStringMap := Some(simpleStringMap), simpleStringList := Some(stringList), structureList := Some(structureList), very := Some(nested)));
        expect ret.Success?;
        print ret;
    }
}