// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"

module  SimpleEnumImplTest {
    import SimpleEnum
    import StandardLibrary.UInt
    import opened SimpleTypesSmithyEnumTypes
    import opened Wrappers
    method{:test} GetEnum(){
        var client :- expect SimpleEnum.SimpleEnum();
        TestGetEnum(client);
        TestGetEnumFirstKnownValueTest(client);
        TestGetEnumSecondKnownValueTest(client);
        TestGetEnumThirdKnownValueTest(client);
    }

    method TestGetEnum(client: ISimpleTypesEnumClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnum.Types.GetEnumInput(value:= Some(THIRD));
        
        expect convertedEnumInput.value.value == THIRD;

        var ret := client.GetEnum(convertedEnumInput);
        
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(FIRST) == THIRD;
        print ret;
    }

    method TestGetEnumFirstKnownValueTest(client: ISimpleTypesEnumClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnum.Types.GetEnumInput(value:= Some(FIRST));
        
        expect convertedEnumInput.value.value == FIRST;

        var ret := client.GetEnumFirstKnownValueTest(convertedEnumInput);
        
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(THIRD) == FIRST;
        print ret;
    }

    method TestGetEnumSecondKnownValueTest(client: ISimpleTypesEnumClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnum.Types.GetEnumInput(value:= Some(SECOND));
        
        expect convertedEnumInput.value.value == SECOND;

        var ret := client.GetEnumSecondKnownValueTest(convertedEnumInput);
        
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(THIRD) == SECOND;
        print ret;
    }

    method TestGetEnumThirdKnownValueTest(client: ISimpleTypesEnumClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var convertedEnumInput := SimpleEnum.Types.GetEnumInput(value:= Some(THIRD));
        
        expect convertedEnumInput.value.value == THIRD;

        var ret := client.GetEnumThirdKnownValueTest(convertedEnumInput);
        
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(FIRST) == THIRD;
        print ret;
    }
}
