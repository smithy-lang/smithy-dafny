
include "../../libraries/src/Wrappers.dfy"

module StandardLibrary.Actions {

  import opened Wrappers

  // TODO: Add to actual Actions library:
  // useful pattern to add an Action<Command, Result> facade
  // to a set of methods that participate in a protocol.
  // Then you have a history that ties the behavior
  // of the methods together,
  // supporting constraints on the order of calls etc.
  trait {:termination false} Action<T, R> {
    // ghost var history: seq<(T, R)>

    // predicate Consumes(history: seq<(T, R)>, next: T)
    // predicate Produces(history: seq<(T, R)>)
    var Repr: set<object>

    method Call(t: T) returns (r: R)
      modifies Repr
      // requires Consumes(history, t)

  }

  // TODO: could use different words for calling when there is no input/no output
  method Call<T>(a: Action<T, ()>, t: T) modifies a.Repr {
    var _ := a.Call(t);
  }

  type SingleUseAction<T, R> = a: Action<T, R>
    // TODO: Needs indirection or (!new)
    // TODO: Not quite right, SingleUseAction should be a way of saying
    // "I will only call this once"
    // | forall history | a.Produces(history) :: |history| <= 1
    | true 
    witness *

  class SeqEnumerator<T> extends Action<(), Option<T>> {

    var values: seq<T>

    constructor(values: seq<T>) {
      this.values := values;
    }

    method {:verify false} Call(input: ()) returns (value: Option<T>) 
      modifies Repr
    {
      if |values| == 0 {
        value := None;
      } else {
        value := Some(values[0]);
        values := values[1..];
      }
    }

  }


  // TODO: This is a finite stream really,
  // ideally this would be a specific instance of an infinite stream
  // of Option<T> just like Action<(), T>
  // TODO: Do we need to signal back pressure or cancellation?
  // Could return something from OnNext
  trait Stream<T> {

    var Repr: set<object>

    method Put(t: T)
      modifies Repr

    method OnNext(a: Action<T, ()>)
      modifies Repr, a.Repr

  }

  // Similar to Result, but for delivering a sequence of values instead of just one
  type StreamEvent<T, E> = Option<Result<T, E>>

  // Cheating for now, since this can't block
  class SimpleStream<T(0)> extends Stream<T> {

    var values: seq<T>
    var callbacks: seq<Action<T, ()>>

    constructor() {
      values := [];
    }

    predicate Valid() 
      reads this, Repr
    {
      && this in Repr
      && forall a <- callbacks :: a in Repr && a.Repr <= Repr
    }

    method {:verify false} Put(value: T)
      modifies Repr
    {
      values := values + [value];

      for i := 0 to |callbacks| 
        invariant callbacks == old(callbacks)
      {
        var callback := callbacks[i];
        var _ := callback.Call(value);
      }
    }

    method OnNext(a: Action<T, ()>)
      modifies Repr
    {
      assume Valid();
      callbacks := callbacks + [a];
    }

  }

  class LazyStream<T(0)> extends Stream<Option<T>> {

    const iter: Action<(), Option<T>>
    var callbacks: seq<Action<Option<T>, ()>>

    constructor(iter: Action<(), Option<T>>) {
      this.iter := iter;
    }

    predicate Valid() 
      reads this, Repr
    {
      && this in Repr
      && iter in Repr && iter.Repr <= Repr
      && forall a <- callbacks :: a in Repr && a.Repr <= Repr
    }

    method Put(value: Option<T>)
      modifies Repr
    {
      expect false;
    }

    method {:verify false} OnNext(a: Action<Option<T>, ()>)
      modifies Repr
    {
      // TODO: Actual Action specs to prove this terminates
      while (true) {
        var next := iter.Call(());
        var _ := a.Call(next);

        if next == None {
          break;
        }
      }
    }

  }
}