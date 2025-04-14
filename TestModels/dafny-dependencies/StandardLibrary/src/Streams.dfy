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

  // TODO: Consider a more generic term for Streamed[Of],
  // especially if we can decouple the filtering out Failures
  // from the concatenation of batches.
  // TODO: Add this to the actual Dafny standard library,
  // since it's generic enough.

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
    const totalLength: Option<uint64>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> ValidHistory(history)
      decreases Repr, 0

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && totalLength.Some? ==> ValidStreamed(outputs, totalLength.value as int)
      decreases Repr

    ghost function Streamed(): seq<T>
      requires Valid()
      reads this, Repr
    {
      StreamedOf(Outputs())  
    }

    method Read(max: uint64) returns (r: Option<Result<seq<T>, E>>)
      requires Requires(())
      // reads Reads(())
      modifies Modifies(())
      decreases Decreases(())
      ensures Ensures((), r)
      ensures 0 < max ==> RemainingDecreasedBy(r)
      ensures r.Some? && r.value.Success? ==> |r.value.value| <= max as int
  }

  ghost function StreamedOf<T, E>(outputs: seq<Option<Result<seq<T>, E>>>): seq<T>
  {
    // This could be defined as something like this instead:
    //
    //   Flatten(MapPartialFunction(x => x.value, Filter(x => x.Success?, ProducedOf(outputs))))
    //
    // But then the lack of extensionality in Dafny hits hard,
    // and it becomes impossible to expand the definition elsewhere.

    if |outputs| == 0 then
      []
    else if outputs[0].Some? && outputs[0].value.Success? then
      outputs[0].value.value + StreamedOf(outputs[1..])
    else
      StreamedOf(outputs[1..])
  }

  ghost predicate ValidStreamed<T, E>(outputs: seq<Option<Result<seq<T>, E>>>, length: int)
    requires Partitioned(outputs, IsSome)
  {
    && var streamed := StreamedOf(outputs);
    && |streamed| <= length
    && (!Seq.All(outputs, IsSome) ==> |streamed| == length)
  }

  lemma StreamedOfSingleton<T, E>(s: seq<T>)
    ensures 
      var singleton: Option<Result<seq<T>, E>> := Some(Success(s));
      StreamedOf([singleton]) == s
  {}

  lemma StreamedOfComposition<T, E>(left: seq<Option<Result<seq<T>, E>>>, right: seq<Option<Result<seq<T>, E>>>)
    ensures StreamedOf(left + right) == StreamedOf(left) + StreamedOf(right)
  {
    if left == [] {
      assert left + right == right;
    } else {
      StreamedOfComposition(left[1..], right);
      assert left == [left[0]] + left[1..];
      assert left + right == [left[0]] + (left[1..] + right);
    }
  } 

  lemma ValidStreamedAfterNone<T, E>(outputs: seq<Option<Result<seq<T>, E>>>, length: int)
    requires Partitioned(outputs, IsSome)
    requires |StreamedOf(outputs)| == length
    ensures Partitioned(outputs + [None], IsSome)
    ensures ValidStreamed(outputs + [None], length)
  {
    var right: seq<Option<Result<seq<T>, E>>> := [None];
    PartitionedCompositionRight(outputs, [None], IsSome);
    assert Partitioned(outputs + [None], IsSome);
    var streamedAfter := StreamedOf(outputs + [None]);
    assert ProducedOf(right) == [];
    StreamedOfComposition(outputs, right);
  }

  lemma ValidStreamedAfterMoreData<T, E>(outputs: seq<Option<Result<seq<T>, E>>>, value: seq<T>, length: int)
    requires All(outputs, IsSome)
    requires 
      (AllImpliesPartitioned(outputs, IsSome); 
      |StreamedOf(outputs)| + |value| <= length)
    requires ValidStreamed(outputs, length)
    ensures Partitioned(outputs + [Some(Success(value))], IsSome)
    ensures ValidStreamed(outputs + [Some(Success(value))], length)
    ensures StreamedOf(outputs + [Some(Success(value))]) == StreamedOf(outputs) + value
  {
    AllImpliesPartitioned(outputs, IsSome);
    var right: seq<Option<Result<seq<T>, E>>> := [Some(Success(value))];
    assert All(right, IsSome);
    PartitionedCompositionLeft(outputs, right, IsSome);
    assert ProducedOf(right) == [Success(value)];
    reveal Seq.Map();
    assert StreamedOf(right) == Flatten([value]);
    reveal Seq.Flatten();
    assert StreamedOf(right) == value + Flatten([]);
    assert StreamedOf(right) == value;
    StreamedOfComposition(outputs, right);
  }

  lemma ValidStreamedAfterFailure<T, E>(outputs: seq<Option<Result<seq<T>, E>>>, error: E, length: int)
    requires All(outputs, IsSome)
    requires 
      (AllImpliesPartitioned(outputs, IsSome); 
      |StreamedOf(outputs)| <= length)
    requires ValidStreamed(outputs, length)
    ensures Partitioned(outputs + [Some(Failure(error))], IsSome)
    ensures ValidStreamed(outputs + [Some(Failure(error))], length)
    ensures StreamedOf(outputs + [Some(Failure(error))]) == StreamedOf(outputs)
  {
    AllImpliesPartitioned(outputs, IsSome);
    var right: seq<Option<Result<seq<T>, E>>> := [Some(Failure(error))];
    assert All(right, IsSome);
    PartitionedCompositionLeft(outputs, right, IsSome);
    assert ProducedOf(right) == [Failure(error)];
    reveal Seq.Map();
    assert StreamedOf(right) == [];
    StreamedOfComposition(outputs, right);
  }

  method Drain<T>(p: Producer<T>)
    requires p.Valid()
    // reads p.Repr
    modifies p.Repr
    ensures p.ValidAndDisjoint()
    ensures p.Done()
    ensures old(p.RemainingMetric()).NonIncreasesTo(p.RemainingMetric())
  {
    while true
      invariant fresh(p.Repr - old(p.Repr))
      invariant p.ValidAndDisjoint()
      decreases p.Remaining()
    {
      var n := p.Next();
      if n.None? { break; }
    }
    assert Last(p.Outputs()) == None;
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

  trait ProducesTotalLengthProof<T, E> {

    const producer: Producer<Result<seq<T>, E>>
    const length: int

    lemma ProducesTotalLength(history: seq<((), Option<Result<seq<T>, E>>)>)
      requires producer.ValidHistory(history)
      ensures ValidStreamed(OutputsOf(history), length)
  }

  /*
   * Wraps an Producer up as a non-rewindable DataStream.
   * It implements Read() using Next(), and buffers extra data as needed.
   */
  class ProducerDataStream<T, E> extends DataStream<T, E> {

    const wrapped: Producer<Result<seq<T>, E>>
    const length: uint64
    var buffer: seq<T>

    ghost const producesTotalLengthProof: ProducesTotalLengthProof<T, E>

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
      && totalLength == Some(length)
      && |buffer| <= length as int
      && StreamedOf(Outputs()) + buffer == StreamedOf(wrapped.Outputs())
      && (0 < |buffer| ==> !wrapped.Done())
      && (!Done() <==> !wrapped.Done())
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, E>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && totalLength.Some? ==> ValidStreamed(outputs, totalLength.value as int)
      decreases Repr
    {
      totalLength.Some? ==> ValidStreamed(outputs, totalLength.value as int)
    }

    ghost function RemainingMetric(): TerminationMetric 
      requires Valid()
      reads this, Repr
      decreases Repr, 3
    {
      TMTuple(TMTop, wrapped.RemainingMetric(), TMNat(|buffer|))
    }

    constructor(wrapped: Producer<Result<seq<T>, E>>, length: uint64, ghost producesTotalLengthProof: ProducesTotalLengthProof<T, E>)
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

      this.totalLength := Some(length);
      this.history := [];
      this.Repr := {this} + wrapped.Repr;
      this.producesTotalLengthProof := producesTotalLengthProof;
    }

    method Invoke(i: ()) returns (r: Option<Result<seq<T>, E>>)
      requires Requires(i)
      // reads this, Repr
      modifies Modifies(i)
      decreases Decreases(i), 0
      ensures Ensures(i, r)
      ensures RemainingDecreasedBy(r)
    {
      assert Requires(());
      assert Valid();
      if length == 0 {
        r := None;

        producesTotalLengthProof.ProducesTotalLength(wrapped.history);
        assert |StreamedOf(wrapped.Outputs())| == 0;
        PartitionedCompositionRight(Outputs(), [None], IsSome);
        StreamedOfComposition(Outputs(), [None]);
        assert OutputsOf(history + [((), None)]) == Outputs() + [None];

        OutputsPartitionedAfterOutputtingNone();
        ProduceNone();

        Drain(wrapped);
        Repr := {this} + wrapped.Repr;
        producesTotalLengthProof.ProducesTotalLength(wrapped.history);
        assert Last(Outputs()) == None;
        assert Done();
        assert Valid();

        reveal TerminationMetric.Ordinal();
        old(RemainingMetric()).TupleNonIncreasesToTuple(RemainingMetric());
      } else {
        r := Read(length);
      }
    }

    @IsolateAssertions
    method Read(max: uint64) returns (r: Option<Result<seq<T>, E>>)
      requires Requires(())
      // reads Reads(())
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
        assert !wrapped.Done();
        next := Some(Success(buffer));
        StreamedOfSingleton<T, E>(buffer);
        buffer := [];

        assert StreamedOf(Outputs()) + StreamedOf([next]) == StreamedOf(wrapped.Outputs());
      } else {
        next := wrapped.Next();
        Repr := {this} + wrapped.Repr;
        producesTotalLengthProof.ProducesTotalLength(wrapped.history);
        
        assert wrapped.Outputs() == old(wrapped.Outputs()) + [next];
        StreamedOfComposition(old(wrapped.Outputs()), [next]);
        assert StreamedOf(wrapped.Outputs()) == StreamedOf(old(wrapped.Outputs())) + StreamedOf([next]);
        assert StreamedOf(Outputs()) + StreamedOf([next]) == StreamedOf(wrapped.Outputs());
      }
      assert StreamedOf(Outputs()) + StreamedOf([next]) == StreamedOf(wrapped.Outputs());
      producesTotalLengthProof.ProducesTotalLength(wrapped.history);
      assert |StreamedOf(wrapped.Outputs())| <= length as int;

      if next.None? {
        r := None;

        ghost var right := [next];
        assert Last(wrapped.Outputs()) == next;
        assert wrapped.Outputs() == old(wrapped.Outputs()) + right;
        assert StreamedOf(wrapped.Outputs()) == StreamedOf(old(wrapped.Outputs()) + right);
        assert StreamedOf(right) == [];
        StreamedOfComposition(old(wrapped.Outputs()), right);
        assert old(|StreamedOf(wrapped.Outputs())|) == old(|StreamedOf(Outputs())|);
        assert StreamedOf(wrapped.Outputs()) == old(StreamedOf(wrapped.Outputs())) + [];
        assert old(|StreamedOf(wrapped.Outputs())|) == |StreamedOf(wrapped.Outputs())|;
        assert |StreamedOf(wrapped.Outputs())| == length as int;
        assert |StreamedOf(Outputs())| == length as int;
        ValidStreamedAfterNone(Outputs(), length as int);
        OutputsPartitionedAfterOutputtingNone();

        assert OutputsOf(history + [((), None)]) == Outputs() + [None];
        assert ValidHistory(history + [((), None)]);
        ProduceNone();

        assert Last(wrapped.Outputs()) == None;
        assert Last(Outputs()) == None;

        assert StreamedOf([r]) == [];
        StreamedOfComposition(old(Outputs()), [r]);

        assert Valid();
      } else {

        assert Last(wrapped.Outputs()).Some?;
        PartitionedLastTrueImpliesAll(wrapped.Outputs(), IsSome);

        assert !wrapped.Done();
        wrapped.DoneIsOneWay();
        assert old(!wrapped.Done());
        assert old(!Done());
        assert !Done();
        assert All(Outputs(), IsSome);

        if next.value.Failure? {
          r := next;

          assert old(Valid());
          assert StreamedOf(old(Outputs())) + old(buffer) == old(StreamedOf(wrapped.Outputs()));
          OutputsPartitionedAfterOutputtingSome(r.value);
          PartitionedCompositionLeft(Outputs(), [r], IsSome);
          StreamedOfComposition(Outputs(), [r]);
          assert StreamedOf(Outputs() + [r]) + buffer == StreamedOf(wrapped.Outputs());

          assert |StreamedOf(wrapped.Outputs())| <= length as int;
          ValidStreamedAfterFailure(Outputs(), next.value.error, length as int);
        } else {
          var size := if max <= |next.value.value| as uint64 then max else |next.value.value| as uint64;
          var result := next.value.value[..size];
          var value := Success(result);
          r := Some(value);
          buffer := next.value.value[size..];
          
          assert next.value.value == next.value.value[..size] + next.value.value[size..];
          StreamedOfSingleton<T, E>(r.value.value);
          StreamedOfSingleton<T, E>(next.value.value);
          assert StreamedOf([r]) + buffer == StreamedOf([next]);

          assert StreamedOf(Outputs()) + StreamedOf([r]) + buffer == StreamedOf(wrapped.Outputs());

          assert old(Valid());
          assert StreamedOf(old(Outputs())) + old(buffer) == old(StreamedOf(wrapped.Outputs()));
          OutputsPartitionedAfterOutputtingSome(value);
          PartitionedCompositionLeft(Outputs(), [r], IsSome);
          StreamedOfComposition(Outputs(), [r]);
          assert StreamedOf(Outputs() + [r]) + buffer == StreamedOf(wrapped.Outputs());

          assert |StreamedOf(wrapped.Outputs())| <= length as int;
          ValidStreamedAfterMoreData(Outputs(), result, length as int);
        }

        assert ValidOutputs(Outputs() + [r]);
        assert OutputsOf(history + [((), r)]) == Outputs() + [r];
        assert ValidHistory(history + [((), r)]);
        ProduceSome(r.value);

        assert Last(wrapped.Outputs()).Some?;
        assert Last(Outputs()).Some?;

        assert Valid();
      }
      
      assert Valid();
      if 0 < max {
        reveal TerminationMetric.Ordinal();
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
      && totalLength == Some(|s| as uint64)
      && position as int <= |s|
      && 0 < chunkSize
      && StreamedOf(Outputs()) == s[..position]
    }

    ghost predicate ValidOutputs(outputs: seq<Option<Result<seq<T>, ()>>>)
      requires Seq.Partitioned(outputs, IsSome)
      ensures ValidOutputs(outputs) && totalLength.Some? ==> ValidStreamed(outputs, totalLength.value as int)
      decreases Repr
    {
      && totalLength.Some?
      && ValidStreamed(outputs, totalLength.value as int)
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
      this.totalLength := Some(|s| as uint64);

      this.history := [];
      this.Repr := {this};
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
      var streamed := StreamedOf(outputs);
      if outputs == [] {
        assert produced == [];
      } else {
        assert outputs == [Some(Success(s[..position]))];
        StreamedOfSingleton<T, ()>(s[..position]);
      }
    }

    method Invoke(t: ()) returns (r: Option<Result<seq<T>, ()>>)
      requires Requires(t)
      // reads this, Repr
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
      // reads this, Repr
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

        ValidStreamedAfterNone(Outputs(), totalLength.value as int);
        assert OutputsOf(history + [((), None)]) == Outputs() + [None];
        assert ValidHistory(history + [((), None)]);
        ProduceNone();

        assert StreamedOf([r]) == [];
        StreamedOfComposition(old(Outputs()), [r]);
        assert StreamedOf(Outputs()) == s[..position];
      } else {
        var remaining := |s| as uint64 - position;
        var size := if max <= remaining then max else remaining;
        var newPosition := position + size;
        var chunk := Success(s[position..newPosition]);
        r := Some(chunk);
        position := newPosition;

        ValidStreamedAfterMoreData(Outputs(), chunk.value, totalLength.value as int);
        assert OutputsOf(history + [((), r)]) == Outputs() + [r];
        assert ValidHistory(history + [((), r)]);
        ProduceSome(chunk);

        calc {
          StreamedOf(Outputs());
          old(StreamedOf(Outputs())) + chunk.value;
          s[..old(position)] + chunk.value;
          s[..old(position)] + s[old(position)..position];
          s[..position];
        }
        assert StreamedOf(Outputs()) == s[..position];
      }

      reveal TerminationMetric.Ordinal();
      assert Valid();
    }
  }
}