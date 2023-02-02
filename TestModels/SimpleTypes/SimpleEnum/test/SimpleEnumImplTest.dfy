include "../src/Index.dfy"

module  SimpleEnumImplTest {
    import SimpleEnum
    import StandardLibrary.UInt
    import opened SimpleTypesEnumTypes
    import opened Wrappers
    method{:test} GetEnum(){
        var client :- expect SimpleEnum.SimpleEnum();
        TestGetEnum(client);
    }

    method TestGetEnum(client: ISimpleTypesEnumClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var ret := client.GetEnum(SimpleEnum.Types.GetEnumInput(value:= Some(THIRD)));
        expect ret.Success?;
        expect ret.value.value.UnwrapOr(FIRST) == THIRD;
        print ret;
    }
}