include "../src/Index.dfy"

module SimpleExternImplTest {
    import SimpleExtern
    import StandardLibrary.UInt
    import opened SimpleExternTypes
    import opened Wrappers

    method{:test} Extern(){
        var client :- expect SimpleExtern.SimpleExtern();
        TestGetExtern(client);
    }
    
    method TestGetExtern(client: ISimpleExternClient)
        requires client.ValidState()
        modifies client.Modifies
        ensures client.ValidState()
    {
        var ret :- expect client.GetExtern(input := GetExternInput(blobValue:= Some([0,0,7]),
            booleanValue:= Some(true),
            stringValue:= Some("TestStringValue"),
            integerValue:= Some(100),
            longValue:= Some(9000)));
        expect ret.blobValue.UnwrapOr([]) == [0,0,7];
        expect ret.booleanValue.UnwrapOr(false) == true;
        expect ret.stringValue.UnwrapOr([]) == "TestStringValue";
        expect ret.integerValue.UnwrapOr(0) == 100;
        expect ret.longValue.UnwrapOr(0) == 9000;
    }
}