include "../Model/SimpleStreamingTypes.dfy"

module {:options "--function-syntax:4"} Chunker {

  import Std.BoundedInts

  import opened Std.Wrappers
  import opened Types = SimpleStreamingTypes
  import opened StandardLibrary.UInt
  import opened Std.Actions
  import opened Std.BulkActions
  import opened Std.Producers
  import opened Std.Consumers
  import opened Std.Streams

  @AssumeCrossModuleTermination
  class Chunker<E> extends BulkAction<Option<Result<uint8, E>>, Option<Producer<Result<uint8, E>>>> {

    const chunkSize: CountingInteger
    var chunkBuffer: BoundedInts.bytes

    constructor(chunkSize: CountingInteger)
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      this.chunkSize := chunkSize;
      chunkBuffer := [];
      history := [];
      Repr := {this};
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      this in Repr
    }

    ghost predicate ValidHistory(history: seq<(Option<Result<BoundedInts.bytes, E>>, Option<Producer<Result<BoundedInts.bytes, E>>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(Option<Result<BoundedInts.bytes, E>>, Option<Producer<Result<BoundedInts.bytes, E>>>)>, next: Option<Result<BoundedInts.bytes, E>>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(i: Option<Result<BoundedInts.bytes, E>>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    // Ideally could use this in a MappedConsumer as well

    method Single(input: Option<Result<uint8, E>>) returns (r: Option<Producer<Result<uint8, E>>>) 
    {

    }

    method Bulk(input: Producer<Result<uint8, E>>, output: Consumer<Result<uint8, E>>) {
      
    }

    method BulkInvoke(input: Producer<Result<uint8, E>>, output: IConsumer<Result<uint8, E>>)
      requires Requires(input)
      modifies Modifies(input)
      decreases Decreases(input), 0
      ensures Ensures(input, r)
    {
      assert Valid();
      var outputChunks := [];
      if input.Some? {
        if input.value.Failure? {
          outputChunks := outputChunks + [input.value];
        } else {

          chunkBuffer := chunkBuffer + input.value.value;
          
          while chunkSize as int <= |chunkBuffer|
            invariant ValidAndDisjoint()
            invariant history == old(history)
          {
            outputChunks := outputChunks + [Success(chunkBuffer[..chunkSize])];
            chunkBuffer := chunkBuffer[chunkSize..];
          }
        }
      } else {
        if 0 < |chunkBuffer| {
          outputChunks := outputChunks + [Success(chunkBuffer)];
        } else {
          r := None;
          UpdateHistory(input, r);
          return;
        }
      }
      var output := new SeqReader(outputChunks);
      r := Some(output);
      UpdateHistory(input, r);
    }
  }

  @AssumeCrossModuleTermination
  class ChunkerTotalProof<E> extends TotalActionProof<Option<Result<BoundedInts.bytes, E>>, Option<Producer<Result<BoundedInts.bytes, E>>>> {

    ghost const chunker: Chunker<E>

    ghost constructor(chunker: Chunker<E>)
      requires chunker.Valid()
      ensures this.chunker == chunker
      ensures Valid()
      ensures fresh(Repr)
    {
      this.chunker := chunker;
      Repr := {this};
    }

    ghost function Action(): Action<Option<Result<BoundedInts.bytes, E>>, Option<Producer<Result<BoundedInts.bytes, E>>>> {
      chunker
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      this in Repr
    }

    lemma AnyInputIsValid(history: seq<(Option<Result<BoundedInts.bytes, E>>, Option<Producer<Result<BoundedInts.bytes, E>>>)>, next: Option<Result<BoundedInts.bytes, E>>)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}

  }

  method ChunkingStream<E>(chunkSize: CountingInteger, s: DataStream<BoundedInts.uint8, E>)
    requires s.Valid()
    requires s.history == []
  {
    var chunker := new Chunker(chunkSize);
    ghost var chunkerTotalProof := new ChunkerTotalProof(chunker);
    var chunkerStream := new OptionMappedProducer(s, chunker, chunkerTotalProof);
  }

  function SumBits(sum: int, maybeChunk: Result<seq<uint8>, Error>): int {
    match maybeChunk
    case Success(chunk) => sum + BytesBitCount(chunk)
    case Failure(_) => sum
  }

  function BytesBitCount(b: seq<uint8>): int {
    Seq.FoldLeft((sum, byte) => sum + BitCount(byte), 0 as int, b)
  }

  function BitCount(x: uint8): int {
    if x == 0 then
      0
    else if x % 2 == 1 then
      1 + BitCount(x / 2)
    else
      BitCount(x / 2)
  }

  function BinaryOfNumber<E>(x: int32): seq<uint8> {
    // TODO: Actually compute the binary
    [12 as uint8, 34, 56]
  }
}