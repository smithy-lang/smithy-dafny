// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/Index.dfy"
include "../src/WrappedSimpleStreamingImpl.dfy"

module SimpleStreamingImplTest {
    import SimpleStreaming
    import SimpleStreamingImpl
    import Std.Producers
    import Std.Consumers
    import Std.BulkActions
    import opened StandardLibrary.UInt
    import opened StandardLibrary.Streams
    import opened SimpleStreamingTypes
    import opened Wrappers
    method{:test} TestClient(){
        var client :- expect SimpleStreaming.SimpleStreaming();
        TestCountBits(client);
        TestBinaryOf(client);
    }

    method TestCountBits(client: ISimpleStreamingClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: seq<uint8> := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5];
        var stream := new SeqDataStream(s);
        var input: CountBitsInput := CountBitsInput(bits := stream);

        var ret :- expect client.CountBits(input);

        expect ret.sum == 7;
    }

    method TestBinaryOf(client: ISimpleStreamingClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var input: BinaryOfInput := BinaryOfInput(number:=42);

        var ret :- expect client.BinaryOf(input);

        var collector := new BulkActions.BatchSeqWriter<uint8, Error>();
        var collectorTotalProof := new BulkActions.BatchSeqWriterTotalProof(collector);
 
        var reader := ret.binary.Reader();
        reader.ForEach(collector, collectorTotalProof);

        expect collector.elements == [12, 34, 56];
    }

    method TestChunks(client: ISimpleStreamingClient)
      requires client.ValidState()
      modifies client.Modifies
      ensures client.ValidState()
    {
        var s: bytes := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7];
        var stream := new SeqDataStream(s);
        var input: ChunksInput := ChunksInput(bytesIn := stream, chunkSize := 3);

        var ret :- expect client.Chunks(input);

        var collector := new BulkActions.BatchSeqWriter<uint8, Error>();
        var collectorTotalProof := new BulkActions.BatchSeqWriterTotalProof(collector);
 
        var reader := ret.bytesOut.Reader();
        reader.ForEach(collector, collectorTotalProof);

        expect collector.elements == [0x2, 0x1, 0x0, 0x5, 0x4, 0x3, 0x7, 0x6];
    }
}