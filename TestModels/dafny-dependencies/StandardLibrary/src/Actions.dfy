
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

  // Similar to Result, but for delivering a sequence of values instead of just one
  type StreamEvent<T, E> = Option<Result<T, E>>

  // TODO: can backpressure be a meta- stream event?
  type Stream<T> = Action<Action<T, ()>, ()>
    
  method {:verify false} Subscribe<T>(s: Stream<T>, a: Action<T, ()>) {
    var _ := s.Call(a);
  }

  type any

  // // Composition of dispatch and SimpleStream
  // // TODO: DispatchStream or something
  // trait EventEmitter {
  //   var handlers: map<string, Action<any, ()>>
  //   method {:verify false} Emit(name:string, event: any) {
  //     var _ := handlers[name].Call(event);
  //   }
  //   method {:verify false} Listen(name:string, a: Action<any, ()>) {
  //     handlers := handlers[name := a];
  //   }
  // }

  // class RyanStream extends EventEmitter {
    
  //   constructor(a: Action<any, ()>) {
  //     Listen("onData", a);
  //     Listen("onBackpressure", ...);
  //   }
  // }

  // TODO: Convenience utility for piping

  // TODO: Extern in Concurrent that turns a Stream into an Enumerator
  // by collecting values and blocking until
  // one shows up.
  // Might also be useful for ActionPublishers?

  class SimpleStream<T(0)> extends Action<Action<T, ()>, ()> {

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

    method Call(a: Action<T, ()>) returns (nothing: ())
      modifies Repr
    {
      assume Valid();
      callbacks := callbacks + [a];
      return ();
    }

  }

  class LazyStream<T(0)> extends Action<Action<Option<T>, ()>, ()> {

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

    method {:verify false} Call(a: Action<Option<T>, ()>) returns (nothing: ())
      modifies Repr
    {
      // TODO: Actual Action specs to prove this terminates (iter has to be an Enumerable)
      while (true) {
        var next := iter.Call(());
        var _ := a.Call(next);

        if next == None {
          break;
        }
      }
      return ();
    }

  }
}