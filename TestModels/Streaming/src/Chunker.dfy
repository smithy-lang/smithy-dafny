include "../Model/SimpleStreamingTypes.dfy"

module {:options "--function-syntax:4"} Chunker {

  import Std.BoundedInts

  import opened Std.Wrappers
  import opened Types = SimpleStreamingTypes
  import opened StandardLibrary.UInt
  import opened Std.Actions
  import opened Std.Producers

  @AssumeCrossModuleTermination
  class Chunker extends Action<Option<BoundedInts.bytes>, Option<Producer<BoundedInts.bytes>>> {

    const chunkSize: CountingInteger
    var chunkBuffer: BoundedInts.bytes

    constructor(chunkSize: CountingInteger)
      ensures Valid()
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

    ghost predicate ValidHistory(history: seq<(Option<BoundedInts.bytes>, Option<Producer<BoundedInts.bytes>>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(Option<BoundedInts.bytes>, Option<Producer<BoundedInts.bytes>>)>, next: Option<BoundedInts.bytes>)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(i: Option<BoundedInts.bytes>): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    method Invoke(bits: Option<BoundedInts.bytes>) returns (r: Option<Producer<BoundedInts.bytes>>)
      requires Requires(bits)
      modifies Modifies(bits)
      decreases Decreases(bits), 0
      ensures Ensures(bits, r)
    {
      var outputChunks := [];
      if bits.Some? {
        chunkBuffer := chunkBuffer + bits.value;
        
        while chunkSize as int <= |chunkBuffer| 
        {
          outputChunks := outputChunks + [chunkBuffer[..chunkSize]];
          chunkBuffer := chunkBuffer[chunkSize..];
        }
      } else {
        if 0 < |chunkBuffer| {
          outputChunks := outputChunks + [chunkBuffer];
        } else {
          r := None;
          return;
        }
      }

      var output := new SeqReader(outputChunks);
      r := Some(output);
    }
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