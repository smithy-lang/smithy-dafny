// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module {:options "--function-syntax:4"} SimplePositionalImplTest {

    import SimplePositional
    import Types = SimplePositionalTypes
    import opened Wrappers

    method TestClient(client: Types.ISimplePositionalClient) 
        requires client.ValidState()
        modifies client.Modifies
    {
        TestGetResource(client);
        TestGetResourcePositional(client);
        GetIntegerInputPosition(client);
        GetIntegerOutputPosition(client);
    }

    method TestGetResource(client: Types.ISimplePositionalClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := Types.GetResourceInput(
            name := "Test"
        );
        var output :- expect client.GetResource(input);
        var resource: Types.ISimpleResource := output.output;
        var getNameOutput :- expect resource.GetName(Types.GetNameInput());
        expect getNameOutput.name == "Test";
    }

    method TestGetResourcePositional(client: Types.ISimplePositionalClient) 
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := "TestPositional";
        var resource: Types.ISimpleResource :- expect client.GetResourcePositional(input);
        var getNameOutput :- expect resource.GetName(Types.GetNameInput());
        expect getNameOutput.name == "TestPositional";
    }

    method GetIntegerInputPosition(client: Types.ISimplePositionalClient) 
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var input := 5;
        var ret :- expect client.GetIntegerInputPosition(input);
        expect ret.value.UnwrapOr(0) == input;
    }

    method GetIntegerOutputPosition(client: Types.ISimplePositionalClient) 
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var inputInteger:= 5;
        var input := Types.GetIntegerOutputPositionInput(value:= Some(inputInteger));
        var ret :- expect client.GetIntegerOutputPosition(input);
        expect ret == inputInteger;
    }


    method {:test} TestDefaultConfig() {
        var client :- expect SimplePositional.SimplePositional();
        TestClient(client);
    }
}
