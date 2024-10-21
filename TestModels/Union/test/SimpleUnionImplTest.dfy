// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/SimpleResource.dfy"

module SimpleUnionImplTest {
    import SimpleUnion
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
