// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleIntegerImplTest {
    import SimpleInteger
    import opened StandardLibrary.UInt
    import opened SimpleTypesIntegerTypes
    import opened Wrappers
    method{:test} GetInteger(){
        var client :- expect SimpleInteger.SimpleInteger();
        TestGetInteger(client);
        TestGetIntegerKnownValue(client);
        TestGetIntegerEdgeCases(client);
    }

    method TestGetInteger(client: ISimpleTypesIntegerClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetInteger(SimpleInteger.Types.GetIntegerInput(value:= Some(1)));
        expect ret.value.UnwrapOr(0) == 1;
        print ret;
    }

    method TestGetIntegerKnownValue(client: ISimpleTypesIntegerClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret :- expect client.GetIntegerKnownValueTest(SimpleInteger.Types.GetIntegerInput(value:= Some(20)));
        expect ret.value.UnwrapOr(0) == 20;
        print ret;
    }

    method TestGetIntegerEdgeCases(client: ISimpleTypesIntegerClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var inputInteger: seq<int32> :=
            [-1, 0, 1,
             // 2^32-1
             ((UInt.INT32_MAX_LIMIT -1) as int32),
             // -2^32 -1
             -((UInt.INT32_MAX_LIMIT -1) as int32)
            ];
        for i := 0 to |inputInteger| {
            var integerValue: int32 := inputInteger[i];
            print integerValue;

            var ret :- expect client.GetInteger(GetIntegerInput(value:= Some(integerValue)));
            expect ret.value.UnwrapOr(0) == integerValue;
            print ret;
        }

    }
}