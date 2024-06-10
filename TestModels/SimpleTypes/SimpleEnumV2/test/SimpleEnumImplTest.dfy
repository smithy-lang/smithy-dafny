// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleEnumV2ImplTest {
    import SimpleEnumV2
    import StandardLibrary.UInt
    import opened SimpleTypesEnumV2Types
    import opened Wrappers
    method{:test} GetEnum(){
        var client :- expect SimpleEnumV2.SimpleEnumV2();
        TestGetEnum(client);
        TestGetEnumFirstKnownValueTest(client);
        TestGetEnumSecondKnownValueTest(client);
        TestGetEnumThirdKnownValueTest(client);
    }

    method TestGetEnum(client: ISimpleTypesEnumV2Client)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnumV2.Types.GetEnumV2Input(value := Some(THIRD));

        expect convertedEnumInput.value.value == THIRD;

        var ret := client.GetEnumV2(convertedEnumInput);

        expect ret.Success?;
        expect ret.value.value.UnwrapOr(FIRST) == THIRD;
    }

    method TestGetEnumFirstKnownValueTest(client: ISimpleTypesEnumV2Client)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnumV2.Types.GetEnumV2Input(value := Some(FIRST));

        expect convertedEnumInput.value.value == FIRST;

        var ret := client.GetEnumV2FirstKnownValueTest(convertedEnumInput);

        expect ret.Success?;
        expect ret.value.value.UnwrapOr(THIRD) == FIRST;
    }

    method TestGetEnumSecondKnownValueTest(client: ISimpleTypesEnumV2Client)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnumV2.Types.GetEnumV2Input(value := Some(SECOND));

        expect convertedEnumInput.value.value == SECOND;

        var ret := client.GetEnumV2SecondKnownValueTest(convertedEnumInput);

        expect ret.Success?;
        expect ret.value.value.UnwrapOr(THIRD) == SECOND;
    }

    method TestGetEnumThirdKnownValueTest(client: ISimpleTypesEnumV2Client)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnumV2.Types.GetEnumV2Input(value := Some(THIRD));

        expect convertedEnumInput.value.value == THIRD;

        var ret := client.GetEnumV2ThirdKnownValueTest(convertedEnumInput);

        expect ret.Success?;
        expect ret.value.value.UnwrapOr(FIRST) == THIRD;
    }
}
