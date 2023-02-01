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
        TestGetBlobKnownValueTest(client);
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

    method TestGetBlobKnownValueTest(client: ISimpleTypesBlobClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<UInt.uint8> := [0x0, 0x2, 0x4];
        var convertedBlobInput: GetBlobInput := SimpleBlob.Types.GetBlobInput(value:= Some(s));
        SimpleBlobImpl.ValidateBlobType(convertedBlobInput.value.value);
        // Validate values of convertedBlobInput are same as input values
        expect convertedBlobInput.value.value == s;

        var ret :- expect client.GetBlobKnownValueTest(convertedBlobInput);

        // Expect output of GetBlob has same value as input sequence
        // i.e. GetBlob(GetBlobInput(seq)) == GetBlobInput(seq)
        expect ret.value.UnwrapOr([0x0]) == convertedBlobInput.value.value;
        // From above, GetBlobInput(seq) value == seq, so the below should be redundant
        expect ret.value.UnwrapOr([0x0]) == s;
        print ret;
    }

    // TODO: Add Blob tests using externs.
    // 
    // Runtimes often implement blobs using array-like structures. These structures may only be a "view" of a portion
    //   of memory. However, there is a risk that this "view" is implemented incorrectly.
    // For example, a Dafny blob of length 5 (|seq<uint8>| = 5) may be expected to be represented as an (ex.) Java
    //   ByteSequence of length 5. The JRE may have already allocated a large memory buffer and would expect to
    //   allocate memory from this buffer as needed. (This improves allocation speed performance.)
    // However, if the Polymorph layer is incorrect, Polymorph may accidentally request the entire memory buffer,
    //   rather than only 5 bytes. The problem is there is no way to verify whether this has happened from within the
    //   Dafny layer. If Dafny has modelled itself correctly but the error is only detectable from inside the runtime,
    //   Dafny does not understand how to interact with the generated code inside the runtime in a way to verify the
    //   size of the blob (ByteSequence) is expected.
    // The solution is to revisit this test suite after writing externs: https://sim.amazon.com/issues/CrypTool-4911
    // We would write test suites using externs to validate the runtime code is behaving as expected.
}