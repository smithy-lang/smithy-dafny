include "Actions.dfy"
include "../DynamicArray.dfy"

module {:options "--function-syntax:4"} Std.Aggregators {

  import opened Actions
  import opened Wrappers
  import opened DynamicArray

  // TODO: Names need improvement
  type IAggregator<T> = Action<T, ()>
  type Aggregator<T> = Action<T, bool> // | exists limit: nat :: ProducesTerminatedBy(a, r => !r, limit) witness *
  type Accumulator<T> = Action<Option<T>, ()> // | exists limit :: ConsumesTerminatedBy(a, None, limit) witness *
  
  class ArrayAggregator<T> extends Action<T, ()>, ConsumesAllProof<T, ()> {

    var storage: DynamicArray<T>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && storage in Repr
      && this !in storage.Repr
      && storage.Repr <= Repr
      && storage.Valid?()
      && Consumed() == storage.items
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
    {
      var a := new DynamicArray();

      history := [];
      height := 1;
      Repr := {this} + {a} + a.Repr;
      this.storage := a;
    }

    ghost predicate CanConsume(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ()) 
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Consumed() == storage.items;
      storage.Push(t);

      r := ();
      Update(t, r);
      Repr := {this} + {storage} + storage.Repr;
      assert Consumed() == old(Consumed()) + [t];
      assert Valid();
    }

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
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

    ghost function Action(): Action<T, ()> {
      this
    }

    lemma CanConsumeAll(history: seq<(T, ())>, next: T) 
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next) 
    {
    }
  }

  method {:rlimit 0} AggregatorExample() {
    var a: ArrayAggregator<nat> := new ArrayAggregator();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    var _ := a.Invoke(6);
    assert a.Consumed() == [1, 2, 3, 4, 5, 6];
    assert a.storage.items == [1, 2, 3, 4, 5, 6];
  }
}