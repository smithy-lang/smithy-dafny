// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleBooleanImplTest {
    import SimpleBoolean
    import opened SimpleTypesBooleanTypes
    import opened Wrappers
    method{:test} GetBooleanTrue(){
        var client :- expect SimpleBoolean.SimpleBoolean();
        TestGetBooleanTrue(client);
    }
    method{:test} GetBooleanFalse(){
        var client :- expect SimpleBoolean.SimpleBoolean();
        TestGetBooleanFalse(client);
    }

    method TestGetBooleanTrue(client: ISimpleTypesBooleanClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetBoolean(SimpleBoolean.Types.GetBooleanInput(value:= Some(true)));
        expect ret.value.UnwrapOr(false) == true;
        print ret;
    }

    method TestGetBooleanFalse(client: ISimpleTypesBooleanClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetBoolean(SimpleBoolean.Types.GetBooleanInput(value:= Some(false)));
        expect ret.value.UnwrapOr(true) == false;
        print ret;
    }
}