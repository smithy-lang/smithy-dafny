
include "Actions.dfy"
include "Aggregators.dfy"

module {:options "--function-syntax:4"} Std.Enumerators {

  import opened Actions
  import opened Aggregators
  import opened Wrappers

  trait Enumerator<T> extends Action<(), Option<T>>, ProducesTerminatedProof<(), Option<T>> {
    ghost function Action(): Action<(), Option<T>> {
      this
    }
    ghost function FixedInput(): () {
      ()
    }
    ghost function StopFn(): Option<T> -> bool {
      StopWhenNone
    }
    predicate StopWhenNone(r: Option<T>) {
      r.None?
    }

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  class SeqEnumerator<T> extends Enumerator<T> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>) 
      ensures Valid()
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
      history := [];
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
    }
    
    ghost predicate CanConsume(history: seq<((), Option<T>)>, next: ())
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    {
      var index := |history|;
      var values := Min(index, |elements|);
      var nones := index - values;
      && (forall i <- Inputs(history) :: i == ())
      && Outputs(history) == Seq.Map(x => Some(x), elements[..values]) + Seq.Repeat(None, nones)
    }

    method Invoke(t: ()) returns (value: Option<T>) 
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, value)
    {
      if |elements| <= index {
        value := None;
      } else {
        value := Some(elements[index]);
        index := index + 1;
      }
      Update((), value);
      // TODO: Doable but annoying
      assume CanProduce(history);
      assert Valid();
    }


    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      // reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    ghost function Limit(): nat {
      |elements|
    }

    lemma CanConsumeAll(history: seq<((), Option<T>)>, next: ()) 
      requires Action().CanProduce(history) 
      ensures Action().CanConsume(history, next)
    {}

    lemma ProducesTerminated(history: seq<((), Option<T>)>)
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
    {
      assert Terminated(Outputs(history), StopFn(), |elements|);
    }

  }

  trait {:termination false} Pipeline<U, T> extends Action<(), Option<T>> {
    
    const upstream: Enumerator<U>
    const buffer: Collector<T>

    method {:verify false} Invoke(nothing: ()) returns (t: Option<T>) {
      while (|buffer.values| == 0) {
        var u := upstream.Invoke(());
        Process(u, buffer);

        if u.None? {
          break;
        }
      }

      if 0 < |buffer.values| {
        var next := buffer.Pop();
        return Some(next);
      } else {
        return None;
      }
    }

    // method {:verify false} ForEach(a: Accumulator<T, TV>)
    // {
    //   var a' := new PipelineProcessor(this, a);
    //   upstream.ForEach(a');
    // }

    method Process(u: Option<U>, a: Accumulator<T>)

  }

  class PipelineProcessor<U, T> extends Action<Option<U>, ()> {

    const pipeline: Pipeline<U, T>
    const accumulator: Accumulator<T>

    constructor(pipeline: Pipeline<U, T>, accumulator: Accumulator<T>) {
      this.pipeline := pipeline;
      this.accumulator := accumulator;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr 
    }

    ghost predicate CanConsume(history: seq<(Option<U>, ())>, next: Option<U>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(Option<U>, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(u: Option<U>) returns (nothing: ()) {
      pipeline.Process(u, accumulator);
    }

    method RepeatUntil(t: Option<U>, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<Option<U>, ()>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      // reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }

  class FunctionalEnumerator<S, T> extends Action<(), Option<T>> {

    const stepFn: S -> Option<(S, T)>
    var state: S

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr
    }

    constructor(state: S, stepFn: S -> Option<(S, T)>) {
      this.state := state;
      this.stepFn := stepFn;
    }

    ghost predicate CanConsume(history: seq<((), Option<T>)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    {
      true
    }

    method Invoke(t: ()) returns (r: Option<T>) 
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      var next := stepFn(state);
      match next {
        case Some(result) => {
          var (newState, result') := result;
          state := newState;
          r := Some(result');
        }
        case None => {
          r := None;
        }
      }
      Update(t, r);
    }

    method RepeatUntil(t: (), stop: Option<T> -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<(), Option<T>>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      // reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }
  }
}