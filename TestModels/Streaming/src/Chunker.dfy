include "../Model/SimpleStreamingTypes.dfy"

// Separate module not just for better code organization,
// but also to work around the conflict between the Dafny standard library
// Std.Wrappers module and the smithy-dafny specific Wrappers module:
// it's not currently possible to use both Result types in the same module.

module {:options "--function-syntax:4"} Chunker {

  import opened Std.Wrappers
  import opened Types = SimpleStreamingTypes
  import opened StandardLibrary.UInt
  import opened Std.Actions
  import opened Std.BulkActions
  import opened Std.Producers
  import opened Std.Consumers
  import opened StandardLibrary.Streams

  // "Batched Byte"
  type BB = Batched<uint8, Error>

  @AssumeCrossModuleTermination
  class Chunker extends BulkAction<BB, Producer<BB>> {

    const chunkSize: CountingInteger
    var chunkBuffer: seq<uint8>

    constructor(chunkSize: CountingInteger)
      requires 0 < chunkSize
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
      && this in Repr
      && 0 < chunkSize
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==> old(Valid()) && Valid()
      ensures ValidChange() ==> fresh(Repr - old(Repr))
      ensures ValidChange() ==> old(history) <= history
    {
      && fresh(Repr - old(Repr))
      && old(Valid())
      && Valid()
      && old(history) <= history
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    ghost predicate ValidHistory(history: seq<(BB, Producer<BB>)>)
      decreases Repr
    {
      true
    }

    ghost predicate ValidInput(history: seq<(BB, Producer<BB>)>, next: BB)
      requires ValidHistory(history)
      decreases Repr
    {
      true
    }

    ghost function Decreases(i: BB): ORDINAL
      requires Requires(i)
      reads Reads(i)
    {
      0
    }

    @IsolateAssertions
    method Invoke(i: BB) returns (o: Producer<BB>)
      requires Requires(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, o)
    {
      assert Valid();
      var input := new SeqReader([i]);
      var output := new SeqWriter();
      var outputTotalProof := new SeqWriterTotalActionProof(output);
      label before:
      BulkInvoke(input, output, outputTotalProof);
      assert |output.values| == 1;
      o := output.values[0];
      assert Seq.Last(output.Inputs()) == o;
      assert Seq.Last(Inputs()) == i;
    }

    @ResourceLimit("1e9")
    @IsolateAssertions
    method BulkInvoke(input: Producer<BB>,
                      output: IConsumer<Producer<BB>>,
                      outputTotalProof: TotalActionProof<Producer<BB>, ()>)
      requires Valid()
      requires input.Valid()
      requires output.Valid()
      requires outputTotalProof.Valid()
      requires outputTotalProof.Action() == output
      requires Repr !! input.Repr !! output.Repr !! outputTotalProof.Repr
      modifies Repr, input.Repr, output.Repr, outputTotalProof.Repr
      ensures ValidChange()
      ensures input.ValidChange()
      ensures output.ValidChange()
      ensures input.Done()
      ensures input.NewProduced() == NewInputs()
      ensures |input.NewProduced()| == |output.NewInputs()|
      ensures output.NewInputs() == NewOutputs()
    {
      assert Valid();

      var oldProducedCount := input.ProducedCount();
      var batchWriter := new BatchSeqWriter();
      var batchWriterTotalProof := new BatchSeqWriterTotalProof(batchWriter);
      label before:
      input.ForEach(batchWriter, batchWriterTotalProof);
      label after:
      assert input.ValidChange@before();
      assert input.ValidChange();
      input.ProducedAndNewProduced@before();

      var newProducedCount := input.ProducedCount() - oldProducedCount;
      assert newProducedCount == input.NewProducedCount();
      if newProducedCount == 0 {
        // No-op
        assert input.ValidChange();
        assert |batchWriter.Inputs()| == 0;
        assert input.NewProduced() == batchWriter.Inputs();
        assert |input.NewProduced()| == 0;
        output.ValidImpliesValidChange();
        return;
      }

      chunkBuffer := chunkBuffer + batchWriter.elements;

      var chunks, leftover := Chunkify(chunkBuffer);
      var chunkBuffer := leftover;

      var outputProducer: Producer<BB>;
      match batchWriter.state {
        case Failure(error) =>
          outputProducer := new SeqReader([BatchError(error)]);
        case Success(more) =>
          if !more && 0 < |chunkBuffer| {
            // To make it more interesting, produce an error if outputChunks is non empty?
            chunks := chunks + Seq.Reverse(chunkBuffer);
          }
          outputProducer := new BatchReader(chunks);
      }

      var empty := new EmptyProducer();
      var padding: Producer<Producer<BB>> := new RepeatProducer(newProducedCount - 1, empty);
      var producerProducer := new SeqReader([outputProducer]);
      var concatenated: Producer<Producer<BB>> := new ConcatenatedProducer(padding, producerProducer);
      assert producerProducer.Remaining() == Some(1);
      assert padding.Remaining() == Some(newProducedCount - 1);
      assert concatenated.Remaining() == Some(newProducedCount);
      label beforeOutput:
      concatenated.ForEach(output, outputTotalProof);
      assert concatenated.ValidChange@beforeOutput();
      concatenated.ProducedAndNewProduced@beforeOutput();

      assert |input.NewProduced()| == newProducedCount;
      assert |concatenated.NewProduced@beforeOutput()| == newProducedCount;
      assert |input.NewProduced()| == |output.NewInputs()|;
      history := history + Seq.Zip(input.NewProduced(), output.NewInputs());
      assert input.NewProduced() == NewInputs();
    }

    method Chunkify(data: seq<uint8>) returns (chunks: seq<uint8>, leftover: seq<uint8>)
      requires Valid()
    {
      leftover := data;
      chunks := [];
      while chunkSize as int <= |leftover|
        decreases |leftover|
      {
        chunks := chunks + Seq.Reverse(leftover[..chunkSize]);
        leftover := leftover[chunkSize..];
      }
    }
  }

  @AssumeCrossModuleTermination
  class ChunkerTotalProof extends TotalActionProof<BB, Producer<BB>> {

    ghost const chunker: Chunker

    ghost constructor(chunker: Chunker)
      requires chunker.Valid()
      ensures this.chunker == chunker
      ensures Valid()
      ensures fresh(Repr)
    {
      this.chunker := chunker;
      Repr := {this};
    }

    ghost function Action(): Action<BB, Producer<BB>> {
      chunker
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      this in Repr
    }

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))
    {
      old(Valid()) && Valid() && fresh(Repr - old(Repr))
    }

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()
    {}

    lemma AnyInputIsValid(history: seq<(BB, Producer<BB>)>, next: BB)
      requires Valid()
      requires Action().ValidHistory(history)
      ensures Action().ValidInput(history, next)
    {}
  }


  @AssumeCrossModuleTermination
  class ChunkingStream extends DataStream<uint8, Error> {

    const chunkSize: CountingInteger
    const original: DataStream<uint8, Error>

    constructor (original: DataStream<uint8, Error>, chunkSize: CountingInteger)
    {
      this.original := original;
      this.chunkSize := chunkSize;
    }

    function ContentLength(): Option<nat> {
      original.ContentLength()
    }

    predicate Replayable() {
      original.Replayable()
    }

    method Reader() returns (p: Producer<BB>)
      ensures
        && p.Valid()
        && fresh(p.Repr)
        && p.history == []
        && (ContentLength().Some? ==> p.Remaining() == Some(ContentLength().value as int + 1))
    {
      var chunker := new Chunker(chunkSize);
      var chunkerTotalProof := new ChunkerTotalProof(chunker);
      var originalProducer := original.Reader();
      var chunkerStream := new MappedProducer(originalProducer, chunker, chunkerTotalProof);
      // p := new FlattenedProducer(chunkerStream);
    }
  }

  function BitCount(x: uint8): int {
    if x == 0 then
      0
    else if x % 2 == 1 then
      1 + BitCount(x / 2)
    else
      BitCount(x / 2)
  }

  function BinaryOfNumber(x: int32): seq<uint8> {
    // TODO: Actually compute the binary
    [12 as uint8, 34, 56]
  }
}