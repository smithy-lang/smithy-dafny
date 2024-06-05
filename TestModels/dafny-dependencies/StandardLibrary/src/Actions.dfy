
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

  class ComposedAction<T, M, R> extends Action<T, R> {

    const first: Action<T, M>
    const second: Action<M, R>

    constructor(first: Action<T, M>, second: Action<M, R>) {
      this.first := first;
      this.second := second;
    }

    method {:verify false} Call(input: T) returns (r: R) 
      modifies Repr
    {
      var m := first.Call(input);
      r := second.Call(m);
    }

  }

  class FunctionAction<T, R> extends Action<T, R> {

    const f: T -> R

    constructor(f: T -> R) {
      this.f := f;
    }

    method {:verify false} Call(input: T) returns (r: R) 
      modifies Repr
    {
      r := f(input);
    }

  }

  // TODO: Basic spec of a Stream having a pending sequence of events,
  // and hence each action subscribed will EVENTUALLY have Consumed that sequence.
  trait {:termination false} Stream<T> {
    ghost var Repr: set<object>

    method Next() returns (t: Option<T>)

    // TODO: Would be even better if this was a static extern that defaulted
    // to DefaultForEach(this, a)
    method ForEach(a: Action<T, ()>)
  }

  /// Similar to Result, but for delivering a sequence of values instead of just one.
  // This works better (as opposed to Result<Option<T>, E>)
  // because then a stream that can error is just an Enumerable<Result<T, E>>.
  type StreamEvent<T, E> = Option<Result<T, E>>

  method {:verify false} DefaultForEach<T>(s: Stream<T>, a: Action<T, ()>) {
    // TODO: Actual Action specs to prove this terminates (iter has to be an Enumerable)
    while (true) {
      var next := s.Next();
      if next == None {
        break;
      }

      var _ := a.Call(next.value);
    }
  }

  class SimpleStream<T(0)> extends Stream<T> {

    const iter: Action<(), Option<T>>

    constructor(iter: Action<(), Option<T>>) {
      this.iter := iter;
    }

    method {:verify false} Next() returns (t: Option<T>) {
      t := iter.Call(());
    }

    method {:verify false} ForEach(a: Action<T, ()>)
    {
      DefaultForEach(this, a);
    }

  }

  class EmptyStream<T> extends Stream<T> {

    constructor() {}

    method {:verify false} Next() returns (t: Option<T>) {
      t := None;
    }

    method {:verify false} ForEach(a: Action<T, ()>)
    {
      // No-op
    }

  }

  class CollectingAction<T> extends Action<T, ()> {

    var values: seq<T>

    constructor() {
      values := [];
    }

    method {:verify false} Call(t: T) returns (nothing: ()) {
      values := values + [t];
    }

    method {:verify false} Pop() returns (t: T) 
      requires 0 < |values|
    {
      t := values[0];
      values := values[1..];
    }

  }

  trait {:termination false} BlockingPipeline<U, T> extends Stream<T> {

    const upstream: Stream<U>
    const buffer: CollectingAction<T>

    method {:verify false} Next() returns (t: Option<T>) {
      if 0 < |buffer.values| {
        var next := buffer.Pop();
        return Some(next);
      }

      while (|buffer.values| == 0) {
        var u := upstream.Next();
        if u.None? {
          break;
        }
        Process(u.value, buffer);
      }

    }

    method {:verify false} ForEach(a: Action<T, ()>)
    {
      // TODO: Actual Action specs to prove this terminates (iter has to be an Enumerable)
      while (true) {
        var next := upstream.Next();
        if next == None {
          break;
        }

        Process(next.value, a);
      }
    }

    method Process(u: U, a: Action<T, ()>)

  }
}