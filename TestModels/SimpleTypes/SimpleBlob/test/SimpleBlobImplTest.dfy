include "../src/Index.dfy"

module  SimpleBlobImplTest {
    import SimpleBlob
    import StandardLibrary.UInt
    import opened SimpleTypesBlobTypes
    import opened Wrappers
    method{:test} GetBlob(){
        var client :- expect SimpleBlob.SimpleBlob();
        TestGetBlob(client);
    }

    method TestGetBlob(client: ISimpleTypesBlobClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<UInt.uint8> := [0x0, 0x1, 0x2];
        var ret :- expect client.GetBlob(SimpleBlob.Types.GetBlobInput(value:= Some(s)));
        expect ret.value.UnwrapOr([0x0]) == [0x0, 0x1, 0x2];
        print ret;
    }
}