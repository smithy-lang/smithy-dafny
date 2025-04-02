/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// TODO: Relocate under Actions/ instead, I don't think Streams has to be a separate library?
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
  // that requires the ability to replay the enumeration,
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

    ghost const data: seq<T>

    // The total length of all produced batches
    function ContentLength(): (res: Option<uint64>)
      requires Valid()
      reads this, Repr

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) ==> ValidDataSoFar(outputs)
      decreases Repr

    ghost predicate ValidDataSoFar(outputs: seq<Option<Result<seq<T>, E>>>)
      requires Partitioned(outputs, IsSome)
    {
      var produced := ProducedOf(outputs);
      && var dataSoFar := DataSoFar(produced);
      && (dataSoFar.Some? ==> 
        && dataSoFar.value <= data
        && (!Seq.All(outputs, IsSome) ==> dataSoFar.value == data))
    }

    ghost function DataSoFar(produced: seq<Result<seq<T>, E>>): Option<seq<T>>
    {
      if exists o <- produced :: o.Failure? then
        None
      else
        Some(Flatten(MapPartialFunction((o: Result<seq<T>, E>) requires o.Success? => o.value, produced)))
    }
  }

  trait RewindableDataStream<T, E> extends DataStream<T, E> {

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      ensures Valid() ==> |data| <= UINT64_MAX as int
      decreases Repr, 0

    function ContentLength(): (res: Option<uint64>)
      requires Valid()
      reads this, Repr
      ensures res == Some(|data| as uint64)

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

  /*
   * Wraps an Producer up as a non-rewindable DataStream that cannot error.
   */
  class ProducerDataStream<T> extends DataStream<T, ()> {

    const wrapped: Producer<seq<T>>
    const length: uint64

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && ValidHistory(history)
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, ()>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) ==> ValidDataSoFar(outputs)
      decreases Repr
    {
      ValidDataSoFar(outputs)
    }

    ghost function RemainingMetric(): TerminationMetric 
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMSucc(wrapped.RemainingMetric())
    }

    constructor(wrapped: Producer<seq<T>>, length: uint64)
      requires wrapped.Valid()
      requires wrapped.history == []
      ensures Valid()
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.length := length;

      this.history := [];
      this.Repr := {this} + wrapped.Repr;
    }

    function ContentLength(): (res: Option<uint64>)
      requires Valid()
      reads this, Repr
    {
      Some(length)
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
        old(RemainingMetric()).SuccDecreasesToSucc(RemainingMetric());
      } else {
        old(RemainingMetric()).SuccNonIncreasesToSucc(RemainingMetric());
      }
    }
  }

  /*
   * Rewindable stream of a sequence with a configured chunk size.
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
      && position as int <= |s|
      && 0 < chunkSize
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, ()>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) ==> ValidDataSoFar(outputs)
      decreases Repr
    {
      ValidDataSoFar(outputs)
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
        assert (forall o <- produced :: o.Success? ==> 0 < |o.value|);
      } else {
        assert outputs == [Some(Success(s[..position]))];
        assert produced == [Success(s[..position])];
        assert MapPartialFunction((o: Result<seq<T>, ()>) requires o.Success? => o.value, produced) == [s[..position]];
        assert Flatten([s[..position]]) == s[..position];
        assert dataSoFar == Some(s[..position]);
      }
    }

    method Invoke(t: ()) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t), 0
      ensures Ensures(t, r)
      ensures RemainingDecreasedBy(r)
    {
      assert Requires(t);

      assert Valid();
      if position == |s| as uint64 {
        r := None;
      } else {
        // Warning: unbounded integers
        var size := Math.Min(chunkSize as int, |s| - position as int) as uint64;
        var newPosition := position + size;
        r := Some(Success(s[position..newPosition]));
        position := newPosition;
      }
      UpdateHistory(t, r);

      reveal TerminationMetric.Ordinal();

      // TODO: Work to do
      assume {:axiom} Ensures(t, r);
    }
  }
}