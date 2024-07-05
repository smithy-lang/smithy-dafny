
include "../../../libraries/src/Wrappers.dfy"

include "../Frames.dfy"
include "GenericAction.dfy"
include "DecreasesClauses.dfy"
include "../DynamicArray.dfy"
include "../Seq.dfy"

module {:options "--function-syntax:4"} Std.Actions {

  import opened Wrappers
  import opened Frames
  import opened GenericActions
  import opened Termination
  import opened DynamicArray
  import Seq

  // TODO: Documentation, especially overall design
  trait {:termination false} Action<T, R> extends GenericAction<T, R>, Validatable {

    ghost var history: seq<(T, R)>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0

    // KEY DESIGN POINT: these predicates specifically avoid reading the current
    // state of the action.
    // That's so extrisnic properties of an action do NOT depend on their current state.
    // This is key to ensure that you can prove properties of a given action that
    // will continue to hold as the Dafny heap changes.
    // This approach works because Dafny understands that for a given object,
    // the implementation of CanConsume/CanProduce cannot change over time.
    //
    // The downside is that these are then forced to use quantifiers
    // to talk about all possible states of an action.
    // The solution is the trait proof pattern,
    // where a trait is passed around with an abstract lemma
    // that can be invoked on the otherwise quantified state as needed.

    // TODO: Necessary but not sufficient that:
    // CanConsume(history, nextIn) ==> exists nextOut :: CanProduce(history + [(nextIn, nextOut)])
    // Does that need to be explicitly part of the spec?
    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
      decreases height

    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height

    ghost predicate Requires(t: T)
      reads Reads(t) 
    {
      && Valid()
      && CanConsume(history, t)
    }
    ghost function Reads(t: T): set<object> 
      reads this
      ensures this in Reads(t)
    {
      {this} + Repr
    }
    ghost function Modifies(t: T): set<object> 
      reads Reads(t)
    {
      Repr
    }
    ghost function Decreases(t: T): TerminationMetric 
      reads Reads(t)
    {
      NatTerminationMetric(height)
    }
    twostate predicate Ensures(t: T, new r: R) 
      reads Reads(t)
    {
      && Valid()
      && history == old(history) + [(t, r)]
      && fresh(Repr - old(Repr))
    }

    // Possibly optimized extensions

    // // Equivalent to DefaultRepeatUntil below, but may be implemented more efficiently.
    // method RepeatUntil(t: T, stop: R -> bool)
    //   requires Valid()
    //   requires EventuallyStops(this, t, stop)
    //   requires forall i <- Consumed() :: i == t
    //   // reads Reads(t)
    //   modifies Repr
    //   ensures Valid()
    //   //ensures history == old(history) + (n copies of t)/(n - 1 not stop values + stop)

    // Helpers

    ghost method Update(t: T, r: R)
      modifies `history
      ensures history == old(history) + [(t, r)]
    {
      history := history + [(t, r)];
    }

    ghost function Consumed(): seq<T> 
      reads this
    {
      Inputs(history)
    }

    ghost function Produced(): seq<R> 
      reads this
    {
      Outputs(history)
    }
  }

  // method DefaultRepeatUntil<T, R>(a: Action<T, R>, t: T, stop: R -> bool) 
  //   requires a.Valid()
  //   requires EventuallyStops(a, t, stop)
  //   requires forall i <- a.Consumed() :: i == t
  //   // reads a.Repr
  //   modifies a.Repr
  //   ensures a.Valid()
  // {
  //   // TODO: loops need to support reads clauses as well!

  //   while (true) 
  //     modifies a.Repr
  //     invariant a.Valid()
  //     invariant fresh(a.Repr - old(a.Repr))
  //     invariant forall i <- a.Consumed() :: i == t
  //     decreases InvokeUntilTerminationMetric(a, t, stop)
  //   {
  //     label beforeInvoke:
  //     assert a.Valid();
  //     var next := a.Invoke(t);
  //     var nextV := next;
  //     if stop(nextV) {
  //       break;
  //     }
  //     InvokeUntilTerminationMetricDecreased@beforeInvoke(a, t, stop, next);
  //   }
  // }

  // Dependencies stolen from DafnyStandardLibraries
  
  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else a
  }

  function Min(a: int, b: int): int
  {
    if a < b
    then a
    else b
  }

  // Common action invariants

  function Inputs<T, R>(history: seq<(T, R)>): seq<T> {
    Seq.Map((e: (T, R)) => e.0, history)
  }

  function Outputs<T, R>(history: seq<(T, R)>): seq<R> {
    Seq.Map((e: (T, R)) => e.1, history)
  }

  trait ConsumesAllProof<T, R> {
    function Action(): Action<T, R>

    lemma Proof(history: seq<(T, R)>, next: T) 
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next)
  }

  method CallOnce<R>(a: Action<int, R>, ghost p: ConsumesAllProof<int, R>) 
    requires a.Valid()
    requires p.Action() == a
    modifies a, a.Repr
  {
    p.Proof(a.history, 42);
    var x := a.Invoke(42);
  }

  method Main() {
    var a := new ArrayAggregator<int>();
    ghost var proof := ArrayAggregatorConsumesAnythingProof(a);
    assert a == proof.Action();
    CallOnce(a, proof);
  }

  ghost predicate OnlyProduces<T, R>(i: Action<T, R>, history: seq<(T, R)>, c: R) 
  {
    i.CanProduce(history) <==> forall e <- history :: e.1 == c
  }

  ghost predicate Terminated<T>(s: seq<T>, stop: T -> bool, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> stop(s[i])
  }

  lemma TerminatedDistributes<T>(left: seq<T>, right: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(left, stop, |left|)
    requires Terminated(right, stop, n)
    ensures Terminated(left + right, stop, |left| + n)
  {}

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(left + right, stop, n)
    ensures Terminated(left, stop, n)
    ensures Terminated(right, stop, Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  // TODO: generalize to "EventuallyProducesSequence"?
  // ghost predicate ProducesTerminatedBy<T, R>(i: Action<T, R>, stop: R -> bool, limit: nat) {
  //   forall history: seq<(T, R)> | i.CanProduce(history) 
  //     :: exists n: nat | n <= limit :: Terminated(Outputs(history), stop, n)
  // }

  // Class of actions whose precondition doesn't depend on history (probably needs a better name)
  // ghost predicate ContextFree<T, R>(a: Action<T, R>, p: T -> bool) {
  //   forall history, next | a.CanProduce(history)
  //     :: a.CanConsume(history, next) <==> p(next)
  // }

  trait ProducesTerminatedProof<T, R> {

    function Action(): Action<T, R>
    function FixedInput(): T
    function StopFn(): R -> bool
    function Limit(): nat

    lemma Proof(history: seq<(T, R)>) 
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == FixedInput())
      ensures exists n: nat | n <= Limit() :: Terminated(Outputs(history), StopFn(), n)
  }

  trait EventuallyStopsProof<T, R> {

    function Action(): Action<T, R>

    lemma Proof(history: seq<(T, R)>, input: T, stop: R -> bool, limit: nat) 
      requires Action().CanProduce(history) 
      requires (forall i <- Inputs(history) :: i == input)
      ensures exists n: nat | n <= limit :: Terminated(Outputs(history), stop, n)
  }

  // ghost predicate ProducesTerminated<T, R>(e: Action<T, R>, input: T, stop: R -> bool, limit: nat) {
  //   forall history: seq<(T, R)> 
  //     | && e.CanProduce(history) 
  //       && (forall i <- Inputs(history) :: i == input)
  //     ::
  //       exists n: nat | n <= limit :: Terminated(Outputs(history), stop, n)
  // }

  // ghost predicate EventuallyStops<T, R>(a: Action<T, R>, input: T, stop: R -> bool) {
  //   && ConsumesAll(a, input)
  //   && exists limit: nat :: ProducesTerminated(a, input, stop, limit)
  // }

  // ghost function InvokeUntilBound<T, R>(a: Action<T, R>, input: T, stop: R -> bool): (limit: nat)
  //   requires EventuallyStops(a, input, stop)
  //   ensures ProducesTerminated(a, input, stop, limit)
  // {
  //   var limit: nat :| ProducesTerminated(a, input, stop, limit);
  //   limit
  // }

  // ghost function InvokeUntilTerminationMetric<T, R>(a: Action<T, R>, input: T, stop: R -> bool): nat
  //   requires a.Valid()
  //   requires EventuallyStops(a, input, stop)
  //   requires forall i <- a.Consumed() :: i == input
  //   reads a.Repr
  // {
  //   var limit := InvokeUntilBound(a, input, stop);
  //   var n: nat :| n <= limit && Terminated(a.Produced(), stop, n);
  //   TerminatedDefinesNonTerminalCount(a.Produced(), stop, n);
  //   limit - NonTerminalCount(a.Produced(), stop)
  // }

  function NonTerminalCount<T>(produced: seq<T>, stop: T -> bool): nat {
    if |produced| == 0 || stop(produced[0]) then
      0
    else
      1 + NonTerminalCount(produced[1..], stop)
  }

  lemma TerminatedDefinesNonTerminalCount<T>(s: seq<T>, stop: T -> bool, n: nat) 
    requires Terminated(s, stop, n)
    ensures NonTerminalCount(s, stop) == Min(|s|, n)
  {
    if n == 0 || |s| == 0 {
    } else {
      if stop(s[0]) {
      } else {
        assert 1 <= NonTerminalCount(s, stop);
        TerminatedDefinesNonTerminalCount(s[1..], stop, n - 1);
      }
    }
  }

  // twostate lemma InvokeUntilTerminationMetricDecreased<T, R>(a: Action<T, R>, input: T, stop: R -> bool, new nextProduced: R)
  //   requires old(a.Valid())
  //   requires a.Valid()
  //   requires EventuallyStops(a, input, stop)
  //   requires forall i <- old(a.Consumed()) :: i == input
  //   requires a.Consumed() == old(a.Consumed()) + [input]
  //   requires a.Produced() == old(a.Produced()) + [nextProduced]
  //   requires !stop(nextProduced)
  //   ensures InvokeUntilTerminationMetric(a, input, stop) < old(InvokeUntilTerminationMetric(a, input, stop))
  // {
  //   var before := old(a.Produced());
  //   var after := a.Produced();
  //   var limit := InvokeUntilBound(a, input, stop);
  //   var n: nat :| n <= limit && Terminated(before, stop, n);
  //   var m: nat :| m <= limit && Terminated(after, stop, m);
  //   if n < |before| {
  //     assert stop(before[|before| - 1]);
  //     assert !stop(a.Produced()[|a.Produced()| - 1]);
  //     assert |a.Produced()| <= m;
  //     assert !stop(a.Produced()[|before| - 1]);
  //     assert false;
  //   } else {
  //     TerminatedDefinesNonTerminalCount(before, stop, n);
  //     assert NonTerminalCount(before, stop) <= n;
  //     TerminatedDistributes(before, [nextProduced], stop, 1);
  //     assert Terminated(after, stop, |after|);
  //     TerminatedDefinesNonTerminalCount(after, stop, |after|);
  //   }
  // }

  // Aggregators

  // TODO: Names need improvement
  type IAggregator<T> = Action<T, ()>
  // type Aggregator<T> = a: Action<T, bool> | exists limit: nat :: ProducesTerminatedBy(a, r => !r, limit) witness *
  type Accumulator<T> = Action<Option<T>, ()> // | exists limit :: ConsumesTerminatedBy(a, None, limit) witness *

  class ArrayAggregator<T> extends Action<T, ()> {

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

    // method RepeatUntil(t: T, stop: (()) -> bool)
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

  datatype ArrayAggregatorConsumesAnythingProof<T> extends ConsumesAllProof<T, ()> 
         = ArrayAggregatorConsumesAnythingProof(a: ArrayAggregator<T>) {

    function Action(): Action<T, ()> {
      a
    }

    lemma Proof(history: seq<(T, ())>, next: T) 
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

    // method RepeatUntil(t: (), stop: Option<T> -> bool)
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

  class Box {
    const i: nat

    constructor(i: nat) 
      ensures this.i == i
    {
      this.i := i;
    }
  }

  function SeqRange(n: nat): seq<nat> {
    seq(n, i => i)
  }

  lemma SeqRangeIncr(prefix: seq<nat>, n: nat)
    requires prefix == SeqRange(n)
    ensures prefix + [n] == SeqRange(n + 1) 
  {}

  class BoxEnumerator extends Action<(), Box> {

    var nextValue: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && nextValue == |history|
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    {
      nextValue := 0;
      history := [];
      Repr := {this};
      height := 1;
    }

    ghost predicate CanConsume(history: seq<((), Box)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<((), Box)>)
      decreases height
    {
      Seq.Map((b: Box) => b.i, Outputs(history)) == SeqRange(|history|)
    }

    method Invoke(t: ()) returns (r: Box) 
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      ghost var producedBefore := Produced();

      r := new Box(nextValue);
      Update(t, r);
      Repr := {this};
      nextValue := nextValue + 1;

      SeqRangeIncr(Seq.Map((b: Box) => b.i, producedBefore), |producedBefore|);
      assert Valid();
    }

    // method RepeatUntil(t: (), stop: Box -> bool)
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

  method {:rlimit 0} BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Produced()| == 0;
    var a := enum.Invoke(());

    assert enum.Produced() == [a];
    assert Seq.Map((b: Box) => b.i, enum.Produced()) == SeqRange(1) == [0];
    // assert a.i == 0;
    
    // var b := enum.Invoke(());
    // var c := enum.Invoke(());
    // var d := enum.Invoke(());
    // var e := enum.Invoke(());

  }

  // Other primitives/examples todo:
  //  * Promise-like single-use Action<T, ()> to capture a value for reading later
  //  * datatype/codatatype-based enumerations
  //  * Eliminate all the (!new) restrictions - look into "older" parameters?
  //    * How to state the invariant that a constructor as an action creates a new object every time?
  //      * Lemma that takes produced as input, instead of forall produced?
  //  * Enumerable ==> defines e.Enumerator()
  //    * BUT can have infinite containers, probably need IEnumerable as well? (different T for the Action)
  //  * Expressing that an Action "Eventually produces something" (look at how VMC models this for randomness)
  //    * IsEnumerator(a) == "a eventually produces None" && "a then only produces None"
  //    * Build on that to make CrossProduct(enumerable1, enumerable2)
  //  * Example of adapting an iterator
  //  * Example of enumerating all possible values of a type (for test generation)
  //    * Needs to handle infinite types too, hence needs the "eventually produces something" concept
  //  * Document: useful pattern to add an Action<Command, Result> facade
  //        to a set of methods that participate in a protocol.
  //        Then you have a history that ties the behavior
  //        of the methods together,
  //        supporting constraints on the order of calls etc.


  // TODO
  // class Folder<T, R> extends Action<T, bool> {

  //   const f: (R, T) -> R
  //   var value: R

  //   constructor(init: R, f: (R, T) -> R) {
  //     this.f := f;
  //     this.value := init;
  //   }

  //   method {:verify false} Call(t: T) returns (success: bool) {
  //     value := f(value, t);
  //     return success;
  //   }

  // }

  // TODO: This is also a Folder([], (x, y) => x + [y])
  class Collector<T> extends Action<Option<T>, ()> {

    var values: seq<T>

    constructor() {
      values := [];
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr 
    }

    ghost predicate CanConsume(history: seq<(Option<T>, ())>, next: Option<T>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(Option<T>, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(t: Option<T>) returns (nothing: ()) {
      if t.Some? {
        values := values + [t.value];
      }
    }

    // method RepeatUntil(t: Option<T>, stop: (()) -> bool)
    //   requires Valid()
    //   requires EventuallyStops(this, t, stop)
    //   requires forall i <- Consumed() :: i == t
    //   // reads Reads(t)
    //   modifies Repr
    //   ensures Valid()
    // {
    //   DefaultRepeatUntil(this, t, stop);
    // }

    method {:verify false} Pop() returns (t: T) 
      requires 0 < |values|
    {
      t := values[0];
      values := values[1..];
    }

  }

}