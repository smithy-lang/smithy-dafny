
include "../../libraries/src/Wrappers.dfy"

module StandardLibrary.Actions {

  import opened Wrappers

  // TODO: Add to actual Actions library:
  // useful pattern to add an Action<Command, Result> facade
  // to a set of methods that participate in a protocol.
  // Then you have a history that ties the behavior
  // of the methods together,
  // supporting constraints on the order of calls etc.
  trait Action<T, R> {
    ghost var history: seq<(T, R)>

    predicate Consumes(history: seq<(T, R)>, next: T)
    predicate Produces(history: seq<(T, R)>)
    

    method Call(t: T) returns (r: R)
      // requires Consumes(history, t)

  }

  // TODO: could use different words for calling when there is no input/no output
  method Call<T>(a: Action<T, ()>, t: T) {
    var _ := a.Call(t);
  }

  type SingleUseAction<T, R> = a: Action<T, R>
    // TODO: Needs indirection or (!new)
    // TODO: Not quite right, SingleUseAction should be a way of saying
    // "I will only call this once"
    // | forall history | a.Produces(history) :: |history| <= 1
    | true 
    witness *

  predicate ConsumesAnything<T(!new), R(!new)>(a: Action<T, R>) {
    forall history, next | a.Produces(history) :: a.Consumes(history, next)
  }

  // TODO: consumes any None-terminated sequence of inputs
  predicate ConsumesTerminated<T(!new), R(!new)>(a: Action<Option<T>, R>)
}