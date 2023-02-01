include "../src/Index.dfy"

module SimpleBlobImplTest {
    import SimpleBlob
    import SimpleBlobImpl
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
        var convertedBlobInput: GetBlobInput := SimpleBlob.Types.GetBlobInput(value:= Some(s));
        SimpleBlobImpl.ValidateBlobType(convertedBlobInput.value.value);
        // Validate values of convertedBlobInput are same as input values
        expect convertedBlobInput.value.value == s;

        var ret :- expect client.GetBlob(convertedBlobInput);

        // Expect output of GetBlob has same value as input sequence
        // i.e. GetBlob(GetBlobInput(seq)) == GetBlobInput(seq)
        expect ret.value.UnwrapOr([0x0]) == convertedBlobInput.value.value;
        // From above, GetBlobInput(seq) value == seq, so the below should be redundant
        expect ret.value.UnwrapOr([0x0]) == s;
        print ret;
    }
}