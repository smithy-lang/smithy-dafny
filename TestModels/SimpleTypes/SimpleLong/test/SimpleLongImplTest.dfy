// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleLongImplTest {
    import SimpleLong
    import SimpleLongImpl
    import opened StandardLibrary.UInt
    import opened SimpleTypesSmithyLongTypes
    import opened Wrappers
    method{:test} GetLong(){
        var client :- expect SimpleLong.SimpleLong();
        TestGetLong(client);
        TestGetLongEdgeCases(client);
        TestGetLongKnownValueTest(client);
    }

    method TestGetLong(client: ISimpleTypesLongClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var inputLong: int64 := 5;
        var convertedLongInput := SimpleLong.Types.GetLongInput(value:= Some(inputLong));
        SimpleLongImpl.ValidateLongType(convertedLongInput.value.value);
        expect convertedLongInput.value.value == inputLong;

        var ret :- expect client.GetLong(convertedLongInput);
        expect ret.value.UnwrapOr(0) == inputLong;
        print ret;
    }

    method TestGetLongEdgeCases(client: ISimpleTypesLongClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var inputLongs: seq<int64> := 
            [-1, 0, 1,
             // 2^32-1
             (UInt.INT32_MAX_LIMIT as int64) - 1,
             // 2^32
             (UInt.INT32_MAX_LIMIT as int64),
             // 2^32+1
             (UInt.INT32_MAX_LIMIT as int64) + 1,
             // 2^64-1
             ((UInt.INT64_MAX_LIMIT - 1) as int64),
             // -2^32 -1
             -(UInt.INT32_MAX_LIMIT as int64) - 1,
             // -2^32
             -(UInt.INT32_MAX_LIMIT as int64),
             // -2^32 + 1
             -(UInt.INT32_MAX_LIMIT as int64) + 1,
             // -(2^64 - 1) == -2^64 + 1
             -((UInt.INT64_MAX_LIMIT - 1) as int64),
             // -(2^64 - 1) - 1 == -2^64
             -((UInt.INT64_MAX_LIMIT - 1) as int64) - 1
            ];
        for i := 0 to |inputLongs| {
            var inputLong: int64 := inputLongs[i];
            print inputLong;
            var convertedLongInput := SimpleLong.Types.GetLongInput(value:= Some(inputLong));
            SimpleLongImpl.ValidateLongType(convertedLongInput.value.value);
            expect convertedLongInput.value.value == inputLong;

            var ret :- expect client.GetLong(convertedLongInput);
            expect ret.value.UnwrapOr(0) == inputLong;
            print ret;
        }

    }

    method TestGetLongKnownValueTest(client: ISimpleTypesLongClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var inputLong: int64 := 33;
        var convertedLongInput := SimpleLong.Types.GetLongInput(value:= Some(inputLong));
        SimpleLongImpl.ValidateLongType(convertedLongInput.value.value);
        expect convertedLongInput.value.value == inputLong;

        var ret :- expect client.GetLongKnownValueTest(convertedLongInput);
        expect ret.value.UnwrapOr(0) == inputLong;
        print ret;
    }
}
