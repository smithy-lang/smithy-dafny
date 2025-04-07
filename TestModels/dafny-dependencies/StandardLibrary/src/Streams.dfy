/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:options "--function-syntax:4"} Std.Streams {

  import opened Wrappers
  import opened Actions
  import opened Producers
  import opened BoundedInts
  import opened Collections.Seq
  import opened Termination

  //
  // A data stream, i.e. a fallable producer of batches of values.
  //
  // Allows for streams that can only be read once,
  // but see RewindableDataStream for a more specific trait
  // that requires the ability to replay the data,
  // or seek to an arbitrary position (although this may take linear time).
  // That requirement is not in this trait
  // because there are lots of ways to implement a stream
  // where having to replay forces buffering all previous values in memory,
  // which often defeats the purpose of streaming in the first place.
  // In particular, boto3 currently (quite implicitly)
  // requires file-like streams with the ability to seek,
  // but we don't want to force the same requirements on all streams.
  //
  @AssumeCrossModuleTermination
  trait DataStream<T, E> extends Producer<Result<seq<T>, E>> {

    // The total length of all produced batches
    const contentLength: Option<uint64>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && contentLength.Some? ==> ValidDataSoFar(outputs, contentLength.value as int)
      decreases Repr

    method Read(max: uint64) returns (r: Option<Result<seq<T>, E>>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures 0 < max ==> RemainingDecreasedBy(r)
      ensures r.Some? && r.value.Success? ==> |r.value.value| <= max as int
  }

  ghost predicate ValidDataSoFar<T, E>(outputs: seq<Option<Result<seq<T>, E>>>, length: int)
    requires Partitioned(outputs, IsSome)
  {
    var produced := ProducedOf(outputs);
    && var dataSoFar := DataSoFar(produced);
    && (dataSoFar.Some? ==> 
      && |dataSoFar.value| <= length
      && (!Seq.All(outputs, IsSome) ==> |dataSoFar.value| == length))
  }

  ghost function DataSoFar<T, E>(produced: seq<Result<seq<T>, E>>): Option<seq<T>>
  {
    if exists o <- produced :: o.Failure? then
      None
    else
      Some(Flatten(MapPartialFunction((o: Result<seq<T>, E>) requires o.Success? => o.value, produced)))
  }
    
  trait RewindableDataStream<T, E> extends DataStream<T, E> {

    ghost const data: seq<T>

    function Position(): (res: uint64)
      requires Valid()
      reads this, Repr
      ensures res as int <= |data|

    method Seek(newPosition: uint64)
      requires Valid()
      requires newPosition as int <= |data|
      modifies Repr
      ensures Valid()
      ensures Position() == newPosition
  }

  ghost predicate ValidDataLengthSoFar<T>(outputs: seq<Option<seq<T>>>, length: int)
    requires Partitioned(outputs, IsSome)
  {
    var dataSoFar := Flatten(ProducedOf(outputs));
    && |dataSoFar| <= length
    && (!Seq.All(outputs, IsSome) ==> |dataSoFar| == length)
  }

  trait ProducesTotalLengthProof<T> {

    const producer: Producer<seq<T>>
    const length: int

    lemma ProducesTotalLength(history: seq<((), Option<seq<T>>)>)
      requires producer.ValidHistory(history)
      ensures ValidDataLengthSoFar(OutputsOf(history), length)
  }

  /*
   * Wraps an Producer up as a non-rewindable DataStream that cannot error.
   * It implements Read() using Next(), and buffers extra data
   * as needed.
   */
  class ProducerDataStream<T> extends DataStream<T, ()> {

    const wrapped: Producer<seq<T>>
    const length: uint64
    var buffer: seq<T>

    ghost const producesTotalLengthProof: ProducesTotalLengthProof<T>
    ghost const maxWrappedRemaining: TerminationMetric

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && ValidHistory(history)
      && producesTotalLengthProof.producer == wrapped
      && producesTotalLengthProof.length == length as int
      && |buffer| <= length as int
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, ()>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && contentLength.Some? ==> ValidDataSoFar(outputs, contentLength.value as int)
      decreases Repr
    {
      contentLength.Some? ==> ValidDataSoFar(outputs, contentLength.value as int)
    }

    ghost function RemainingMetric(): TerminationMetric 
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMTuple(maxWrappedRemaining, wrapped.RemainingMetric(), TMNat(|buffer|))
    }

    constructor(wrapped: Producer<seq<T>>, length: uint64, ghost producesTotalLengthProof: ProducesTotalLengthProof<T>)
      requires wrapped.Valid()
      requires wrapped.history == []
      requires producesTotalLengthProof.producer == wrapped
      requires producesTotalLengthProof.length == length as int
      ensures Valid()
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.length := length;
      this.buffer := [];

      this.history := [];
      this.Repr := {this} + wrapped.Repr;
      this.producesTotalLengthProof := producesTotalLengthProof;
    }

    method Invoke(i: ()) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(i)
      reads Reads(i)
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, r)
      ensures RemainingDecreasedBy(r)
    {
      assert Requires(i);

      assert Valid();
      var result := wrapped.Next();
      
      r := match result
        case None => None
        case Some(value) => Some(Success(value));
      UpdateHistory(i, r);

      // TODO: work to do
      assume {:axiom} Valid();
      if r.Some? {
        old(RemainingMetric()).TupleDecreasesToTuple(RemainingMetric());
      } else {
        old(RemainingMetric()).TupleNonIncreasesToTuple(RemainingMetric());
      }
    }

    method Read(max: uint64) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(())
      reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures 0 < max ==> RemainingDecreasedBy(r)
      ensures r.Some? && r.value.Success? ==> |r.value.value| <= max as int
    {
      assert Requires(());

      assert Valid();
      var next;
      if 0 < |buffer| {
        next := Some(buffer);
        buffer := [];
      } else {
        next := wrapped.Next();
      }
      assert next.Some? ==> |next.value| <= length as int;

      if next.None? {
        r := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        var size := if max <= |next.value| as uint64 then max else |next.value| as uint64;
        var value := Success(next.value[..size]);
        r := Some(value);
        buffer := next.value[size..];

        OutputsPartitionedAfterOutputtingSome(value);
        ProduceSome(value);
      }
      
      if 0 < max {
        if r.Some? {
          old(RemainingMetric()).TupleDecreasesToTuple(RemainingMetric());
        } else {
          old(RemainingMetric()).TupleNonIncreasesToTuple(RemainingMetric());
        }
      }
      assert 0 < max ==> RemainingDecreasedBy(r);
    }
  }

  /*
   * Rewindable stream of a sequence with a configured default chunk size.
   */
  class SeqDataStream<T> extends RewindableDataStream<T, ()> {

    const s: seq<T>
    const chunkSize: uint64
    var position: uint64

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      ensures Valid() ==> |data| <= UINT64_MAX as int
      decreases Repr, 0
    {
      && this in Repr
      && ValidHistory(history)
      && s == data
      && |s| <= UINT64_MAX as int
      && contentLength == Some(|s| as uint64)
      && position as int <= |s|
      && 0 < chunkSize
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, ()>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && contentLength.Some? ==> ValidDataSoFar(outputs, contentLength.value as int)
      decreases Repr
    {
      && contentLength.Some?
      && ValidDataSoFar(outputs, contentLength.value as int)
    }

    ghost function RemainingMetric(): TerminationMetric 
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMNat(|s| - position as int)
    }

    constructor(s: seq<T>, chunkSize: uint64)
      requires |s| <= UINT64_MAX as int
      requires 0 < chunkSize
      ensures Valid()
    {
      this.data := s;
      this.s := s;
      this.position := 0;
      this.chunkSize := chunkSize;
      this.contentLength := Some(|s| as uint64);

      this.history := [];
      this.Repr := {this};
    }

    function ContentLength(): (res: Option<uint64>)
      requires Valid()
      reads this, Repr
      ensures res == Some(|data| as uint64)
    {
      Some(|s| as uint64)
    }

    function Position(): (res: uint64)
      requires Valid()
      reads this, Repr
      ensures res as int <= |data|
    {
      position
    }

    @ResourceLimit("0")
    method Seek(newPosition: uint64)
      requires Valid()
      requires newPosition as int <= |data|
      modifies Repr
      ensures Valid()
      ensures Position() == newPosition
    {
      position := newPosition;
      if position == 0 {
        history := [];
      } else {
        history := [((), Some(Success(s[..position])))];
      }
      
      var outputs := Outputs();
      var produced := ProducedOf(outputs);
      var dataSoFar := DataSoFar(produced);
      if outputs == [] {
        assert produced == [];
      } else {
        assert outputs == [Some(Success(s[..position]))];
        assert produced == [Success(s[..position])] + ProducedOf([]);
        assert MapPartialFunction((o: Result<seq<T>, ()>) requires o.Success? => o.value, produced) == [s[..position]];
        assert Flatten([s[..position]]) == s[..position];
        assert dataSoFar == Some(s[..position]);
      }
    }

    method Invoke(t: ()) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(t)
      reads this, Repr
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures RemainingDecreasedBy(r)
    {
      assert Valid();
      r := Read(chunkSize);
    }

    method Read(max: uint64) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(())
      reads this, Repr
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures 0 < max ==> RemainingDecreasedBy(r)
      ensures r.Some? && r.value.Success? ==> |r.value.value| <= max as int
    {
      assert Requires(());

      assert Valid();
      if position == |s| as uint64 {
        r := None;

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();
      } else {
        // Warning: unbounded integers
        var remaining := |s| as uint64 - position;
        var size := if max <= remaining then max else remaining;
        var newPosition := position + size;
        var chunk := Success(s[position..newPosition]);
        r := Some(chunk);
        position := newPosition;

        OutputsPartitionedAfterOutputtingSome(chunk);
        ProduceSome(chunk);
      }

      reveal TerminationMetric.Ordinal();
    }
  }
}