
include "Actions.dfy"

module {:options "--function-syntax:4"} Std.Enumerators {

  import opened Actions
  import opened Wrappers

  type IEnumerator<T> = Action<(), T>
  type Enumerator<T> = a: Action<(), Option<T>> | IsEnumerator(a) witness *
  
  ghost predicate IsEnumerator<T>(a: Action<(), Option<T>>) {
    EventuallyStops(a, (), (r: Option<T>) => r.None?)
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  class SeqEnumerator<T> extends Action<(), Option<T>> {

    const elements: seq<T>
    var index: nat

    constructor(elements: seq<T>) 
      ensures Valid()
    {
      this.elements := elements;
      this.index := 0;

      Repr := {this};
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
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
      assert Valid();
    }

    // method RepeatUntil(t: (), stop: Option<TV> -> bool)
    //   requires Valid()
    //   requires EventuallyStops(this, t, stop)
    //   requires forall i <- Consumed() :: i == inputF(t)
    //   // reads Reads(t)
    //   modifies Repr
    //   ensures Valid()
    // {
    //   DefaultRepeatUntil(this, t, stop);
    // }

    lemma ThisIsEnumerator() 
      ensures IsEnumerator(this)
    {
      assert forall history | CanProduce(history) :: CanConsume(history, ());
      var stop := (r: Option<T>) => r.None?;
      forall history: seq<((), Option<T>)> 
      | && CanProduce(history) 
        && (forall i <- Inputs(history) :: i == ()) 
        ensures exists n: nat | n <= |elements| :: Terminated(Outputs(history), stop, n)
      {
        var outputs := Outputs(history);
        assert forall x :: stop(x) == x.None?;
        var index := |history|;
        var values := Min(index, |elements|);
        var nones := index - values;
        assert outputs == Seq.Map(x => Some(x), elements[..values]) + Seq.Repeat(None, nones);
        assert forall i | 0 <= i < |outputs| :: i < values <==> outputs[i].None?;
        assert Terminated(Outputs(history), stop, |elements|);
      }
      assert ProducesTerminated(this, (), (x: Option<T>) => x.None?, |elements|);
    }

  }

  trait {:termination false} Pipeline<U, UV(!new), T, TV(!new)> extends Action<(), Option<T>> {
    

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

  class PipelineProcessor<U, UV(!new), T, TV(!new)> extends Action<Option<U>, ()> {

    const pipeline: Pipeline<U, UV, T, TV>
    const accumulator: Accumulator<T>

    constructor(pipeline: Pipeline<U, UV, T, TV>, accumulator: Accumulator<T>) {
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

    // method RepeatUntil(t: Option<U>, stop: (()) -> bool)
    //   requires Valid()
    //   requires EventuallyStops(this, t, stop)
    //   requires forall i <- Consumed() :: i == t
    //   // reads Reads(t)
    //   modifies Repr
    //   ensures Valid()
    // {
    //   DefaultRepeatUntil(this, t, stop);
    // }
  }
}