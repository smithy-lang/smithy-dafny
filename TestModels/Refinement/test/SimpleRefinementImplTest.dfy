// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module SimpleRefinementImplTest {
    import SimpleRefinement
    import opened SimpleRefinementTypes
    import opened Wrappers
    method{:test} Refinement(){
        var client :- expect SimpleRefinement.SimpleRefinement();
        TestGetRefinement(client);
        TestOnlyInput(client);
        TestOnlyOutput(client);
        TestReadonlyOperation(client);
    }

    method TestGetRefinement(client: ISimpleRefinementClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var res :- expect client.GetRefinement(GetRefinementInput(requiredString := "GetRefinement", optionalString := Some("GetRefinementOptional")));
        print res;
        expect res.requiredString == "GetRefinement";
        expect res.optionalString.UnwrapOr("") == "GetRefinementOptional";
    }

    method TestOnlyInput(client: ISimpleRefinementClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var res :- expect client.OnlyInput(OnlyInputInput(value := Some("InputValue")));
        print res;
    }

    method TestOnlyOutput(client: ISimpleRefinementClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var res :- expect client.OnlyOutput();
        print res;
        expect res.value.UnwrapOr("") == "Hello World";
    }

    method TestReadonlyOperation(client: ISimpleRefinementClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var res :- expect client.ReadonlyOperation(ReadonlyOperationInput(requiredString := "Readonly", optionalString := Some("ReadonlyOptional")));
        print res;
        expect res.requiredString == "Readonly";
        expect res.optionalString.UnwrapOr("") == "ReadonlyOptional";
    }
}