include "Actions.dfy"

module Composed {

  import opened Std.Actions
  import opened Wrappers

  class ComposedAction<T, TV(!new), V, VV(!new), R, RV(!new)> extends Action<T, TV, R, RV> {
    const first: Action<T, TV, V, VV>
    const second: Action<V, VV, R, RV>

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && CanProduce(history)
      && Consumed() == first.Consumed()
      && first.Produced() == second.Consumed()
      && Produced() == second.Produced()
    }

    constructor(second: Action<V, VV, R, RV>, first: Action<T, TV, V, VV>) 
      requires first.Valid()
      requires second.Valid()
      requires first.Repr !! second.Repr
      requires first.history == []
      requires second.history == []
      ensures Valid()
      ensures history == []
    { 
      this.first := first;
      this.second := second;

      history := [];
      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;
    }

    predicate CanConsume(history: seq<(TV, RV)>, next: TV)
      requires CanProduce(history)
      decreases height
    {
      forall piped: seq<VV> | CanPipe(history, piped) :: 
        && var firstHistory := Seq.Zip(Inputs(history), piped);
        && var secondHistory := Seq.Zip(piped, Outputs(history));
        && first.CanConsume(firstHistory, next)
        && forall pipedNext: VV | first.CanProduce(firstHistory + [(next, pipedNext)]) ::
          && second.CanConsume(secondHistory, pipedNext)

      // Note that you can't compose any arbitrary first with a second:
      // if you need to read first.produced to know if you can consume another input,
      // that won't work here because this outer CanConsume predicate doesn't take that as input.
      // (...unless there's a way of inferring what was produced from second.produced)
    }

    predicate CanProduce(history: seq<(TV, RV)>)
      decreases height
    {
      exists piped: seq<VV> :: CanPipe(history, piped)
    }

    predicate CanPipe(history: seq<(TV, RV)>, piped: seq<VV>) 
      decreases height, 0
    {
      && |piped| == |history|
      && first.CanProduce(Seq.Zip(Inputs(history), piped))
      && second.CanProduce(Seq.Zip(piped, Outputs(history)))
    }

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert first.Valid();
      var v := first.Invoke(t);
      r := second.Invoke(v);

      Update(t, r);
      Repr := {this} + first.Repr + second.Repr;
    }

    method RepeatUntil(t: T, stop: RV -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      requires forall i <- Consumed() :: i == inputF(t)
      // reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }
  }

  method Example() {
    var e: SeqEnumerator<int, int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    SeqEnumeratorIsEnumerator(e);
    var f := (x: Option<int>) => match x {
      case Some(v) => Some(v + v)
      case None => None
    };
    var doubler := new FunctionAction(f);
    var mapped: Compose<(), Option<int>, Option<int>> := new Compose(doubler, e);

    // TODO: Need some lemmas
    var x := mapped.Invoke(());
    assert mapped.Produced() == [Some(2)];
    assert [x] == [Some(2)];
    assert x == Some(2);
  }

}