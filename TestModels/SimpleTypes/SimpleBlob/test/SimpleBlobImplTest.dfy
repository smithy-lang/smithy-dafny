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
        var convertedBlobInput: GetBlobInput := SimpleBlob.Types.GetBlobInput(value:= Some(s));
        
        // Validate seq<uint8> type properties on input
        // Input can contain items: "input has a measurable length of at least 0"
        expect |convertedBlobInput.value.value| >= 0;
        // If input has at least one item, then:

        // Validate uint8 type properties on input values
        for i := 0 to |convertedBlobInput.value.value| {
            // Input is index-accessible, which means input is seq-like rather than a set
            var inputElement := convertedBlobInput.value.value[i];
            // "Input can be interpreted as any valid uint8"
            expect inputElement >= 0x0;
        }

        // Expect output of convertedBlobInput has same value as the value it was provided
        // i.e. GetBlobInput(seq) value == seq
        expect convertedBlobInput.value.value == s;

        var ret :- expect client.GetBlob(convertedBlobInput);

        // Expect output of GetBlob has same value as input sequence
        // i.e. GetBlob(GetBlobInput(seq)) == GetBlobInput(seq)
        expect ret.value.UnwrapOr([0x0]) == convertedBlobInput;
        // From above, GetBlobInput(seq) value == seq, so the below should be redundant
        expect ret.value.UnwrapOr([0x0]) == s;
        print ret;
    }
}