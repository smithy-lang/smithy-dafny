// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/SimpleResource.dfy"

module SimpleUnionImplTest {
    import SimpleUnion
    import opened StandardLibrary.UInt
    import SimpleResource
    import opened SimpleUnionTypes
    import opened Wrappers
    method{:test} TestUnion(){
        var client :- expect SimpleUnion.SimpleUnion();
        TestMyUnionInteger(client);
        TestMyUnionString(client);
        TestKnownValueUnionString(client);
    }

    method TestMyUnionInteger(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(IntegerValue(100))));

        expect ret.union.Some?;
        expect ret.union.value.IntegerValue?;
        expect ret.union.value.IntegerValue == 100;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionString(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(StringValue("TestString"))));

        expect ret.union.Some?;
        expect ret.union.value.StringValue?;
        expect ret.union.value.StringValue == "TestString";

        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionBoolean(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(BooleanValue(true))));

        expect ret.union.Some?;
        expect ret.union.value.BooleanValue?;
        expect ret.union.value.BooleanValue == true;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionBlob(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<UInt.uint8> := [0x0, 0x1, 0x2];
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(BlobValue(s))));

        expect ret.union.Some?;
        expect ret.union.value.BlobValue?;
        expect ret.union.value.BlobValue == s;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionDouble(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<UInt.uint8> := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7];
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(DoubleValue(s))));

        expect ret.union.Some?;
        expect ret.union.value.DoubleValue?;
        expect ret.union.value.DoubleValue == s;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionMap(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var stringMap := map["Test1" := "Success"];
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(MapValue(stringMap))));

        expect ret.union.Some?;
        expect ret.union.value.MapValue?;
        expect ret.union.value.MapValue == stringMap;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionLong(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var inputLong: int64 := 5;
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(LongValue(inputLong))));

        expect ret.union.Some?;
        expect ret.union.value.LongValue?;
        expect ret.union.value.LongValue == inputLong;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    
    method TestMyUnionList(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var stringList := ["Test"];
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(ListValue(stringList))));

        expect ret.union.Some?;
        expect ret.union.value.ListValue?;
        expect ret.union.value.ListValue == stringList;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.StructureValue? ==false;
    }

    method TestMyUnionStructure(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var structure := SimpleStruture(Intvalue:= Some(20));
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(StructureValue(structure))));

        expect ret.union.Some?;
        expect ret.union.value.StructureValue?;
        expect ret.union.value.StructureValue == structure;   
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
    }

    method TestMyUnioninsideMyUnion(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<UInt.uint8> := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7];
        var InsideMyUnionValue := MyDouble(s);
        var ret :- expect client.GetUnion(GetUnionInput(union := Some(InsideMyUnion(InsideMyUnionValue))));

        expect ret.union.Some?;
        expect ret.union.value.InsideMyUnion?;
        expect ret.union.value.InsideMyUnion == InsideMyUnionValue;
        expect ret.union.value.IntegerValue? == false;
        expect ret.union.value.StringValue? == false;
        expect ret.union.value.DoubleValue? == false;
        expect ret.union.value.LongValue? == false;
        expect ret.union.value.BooleanValue? == false;
        expect ret.union.value.BlobValue? == false;
        expect ret.union.value.MapValue? == false;
        expect ret.union.value.ListValue? == false;
        expect ret.union.value.StructureValue? == false;
    }

    method TestKnownValueUnionString(client: ISimpleUnionClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetKnownValueUnion(GetKnownValueUnionInput(union := Some(Value(10))));

        expect ret.union.Some?;
        expect ret.union.value.Value?;
        expect ret.union.value.Value == 10;
    }

    // This tests is to support Dafny features.
    // So it does not need to do a lot
    // See the resource for more details.
    method {:test} TestUnionWithResource() {

      var ref := new SimpleResource.SomeResource();
      var inputRef := new SimpleResource.SomeResource();

      var output :- expect ref.GetResourceData(
        GetResourceDataInput(
          requiredUnion := Ref(inputRef),
          optionUnion := Some(Ref(inputRef))
        )
      );
    }

}
