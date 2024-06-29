
include "../../libraries/src/Wrappers.dfy"

include "Frames.dfy"
include "GenericAction.dfy"
include "DecreasesClauses.dfy"
include "DynamicArray.dfy"
include "Seq.dfy"

module {:options "--function-syntax:4"} Std.Actions {

  import opened Wrappers
  import opened Frames
  import opened GenericActions
  import opened Termination
  import opened DynamicArray
  import Seq

  // TODO: Documentation, especially overall design
  trait {:termination false} Action<T, TV(!new), R, RV(!new)> extends GenericAction<T, R>, Validatable {

    ghost var history: seq<(TV, RV)>
    // TODO: Make these --> functions (not ~>, they are useless if they read the heap)
    const inputF: T -> TV
    const outputF: R -> RV

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

    // TODO: Necessary but not sufficient that:
    // CanConsume(history, nextIn) ==> exists nextOut :: CanProduce(history + [(nextIn, nextOut)])
    // Does that need to be explicitly part of the spec?
    ghost predicate CanConsume(history: seq<(TV, RV)>, next: TV)
      requires CanProduce(history)
      decreases height

    ghost predicate CanProduce(history: seq<(TV, RV)>)
      decreases height

    ghost predicate Requires(t: T)
      reads Reads(t) 
    {
      && Valid()
      && CanConsume(history, inputF(t))
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
      && history == old(history) + [(inputF(t), outputF(r))]
      && fresh(Repr - old(Repr))
    }

    // Possibly optimized extensions

    // Equivalent to DefaultRepeatUntil below, but may be implemented more efficiently.
    method RepeatUntil(t: T, stop: RV -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
      //ensures history == old(history) + (n copies of t)/(n - 1 not stop values + stop)

    // Helpers

    ghost method Update(t: T, r: R)
      modifies `history
      ensures history == old(history) + [(inputF(t), outputF(r))]
    {
      history := history + [(inputF(t), outputF(r))];
    }

    ghost function Consumed(): seq<TV> 
      reads this
    {
      Inputs(history)
    }

    ghost function Produced(): seq<RV> 
      reads this
    {
      Outputs(history)
    }
  }

  method DefaultRepeatUntil<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, t: T, stop: RV -> bool) 
    requires a.Valid()
    requires EventuallyStops(a, t, stop)
    reads a, a.Repr
    modifies a.Repr
    ensures a.Valid()
  {
    // TODO: do loops need reads clauses too?
    while (true) 
      invariant a.Valid()
      invariant fresh(a.Repr - old(a.Repr))
      decreases InvokeUntilTerminationMetric(a, t, stop)
    {
      label beforeInvoke:
      assert a.Valid();
      var next := a.Invoke(t);
      var nextV := a.outputF(next);
      if stop(nextV) {
        break;
      }
      InvokeUntilTerminationMetricDecreased@beforeInvoke(a, t, stop, next);
    }
  }

  // Dependencies stolen from DafnyStandardLibraries
  
  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else a
  }

  // Common action invariants

  function Inputs<T, R>(history: seq<(T, R)>): seq<T> {
    Seq.Map((e: (T, R)) => e.0, history)
  }

  function Outputs<T, R>(history: seq<(T, R)>): seq<R> {
    Seq.Map((e: (T, R)) => e.1, history)
  }

  ghost predicate ConsumesAll<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, next: T) {
    forall history | a.CanProduce(history) :: a.CanConsume(history, a.inputF(next))
  }

  ghost predicate OnlyProduces<T, TV(!new), R, RV(!new)>(i: Action<T, TV, R, RV>, history: seq<(TV, RV)>, c: RV) 
  {
    i.CanProduce(history) <==> forall e <- history :: e.1 == c
  }

  ghost predicate CanConsumeAll<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, input: seq<TV>) 
  {
    forall i | 0 < i < |input| ::
      var consumed := input[..(i - 1)];
      var next := input[i];
      forall history | a.CanProduce(history) && Inputs(history) == consumed :: a.CanConsume(history, next)
  }

  ghost predicate Terminated<T>(s: seq<T>, stop: T -> bool, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> stop(s[i])
  }

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, stop: T -> bool, n: nat)
    requires Terminated(left + right, stop, n)
    ensures Terminated(left, stop, n)
    ensures Terminated(right, stop, Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  // TODO: generalize to "EventuallyProducesSequence"?
  ghost predicate ProducesTerminatedBy<T, TV(!new), R, RV(!new)>(i: Action<T, TV, R, RV>, stop: RV -> bool, limit: nat) {
    forall history: seq<(TV, RV)> | i.CanProduce(history) 
      :: exists n: nat | n <= limit :: Terminated(Outputs(history), stop, n)
  }

  // Class of actions whose precondition doesn't depend on history (probably needs a better name)
  ghost predicate ContextFree<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, p: TV -> bool) {
    forall history, next | a.CanProduce(history)
      :: a.CanConsume(history, next) <==> p(next)
  }

  ghost predicate ProducesTerminated<T, TV(!new), R, RV(!new)>(e: Action<T, TV, R, RV>, input: T, stop: RV -> bool, limit: nat) {
    forall history: seq<(TV, RV)> 
      | && e.CanProduce(history) 
        && (forall i <- Inputs(history) :: i == e.inputF(input))
      ::
        exists n: nat, r | n <= limit :: stop(r) && Terminated(Outputs(history), stop, n)
  }

  ghost predicate EventuallyStops<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, input: T, stop: RV -> bool) {
    && ConsumesAll(a, input)
    && exists limit :: ProducesTerminated(a, input, stop, limit)
  }

  ghost predicate IsEnumerator<T, TV(!new)>(a: Action<(), (), Option<T>, Option<TV>>) {
    EventuallyStops(a, (), (r: Option<TV>) => r.None?)
  }

  ghost function InvokeUntilBound<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, input: T, stop: RV -> bool): (limit: nat)
    requires EventuallyStops(a, input, stop)
    ensures ProducesTerminated(a, input, stop, limit)
  {
    var limit: nat :| ProducesTerminated(a, input, stop, limit);
    limit
  }

  ghost function InvokeUntilTerminationMetric<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, input: T, stop: RV -> bool): nat
    requires a.Valid()
    requires EventuallyStops(a, input, stop)
    reads a.Repr
  {
    var limit := InvokeUntilBound(a, input, stop);
    var n: nat :| n <= limit && ProducesTerminated(a,input, stop, n);
    limit - n
  }

  twostate lemma InvokeUntilTerminationMetricDecreased<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, input: T, stop: RV -> bool, new nextProduced: R)
    requires old(a.Valid())
    requires a.Valid()
    requires EventuallyStops(a, input, stop)
    requires a.Produced() == old(a.Produced()) + [a.outputF(nextProduced)]
    requires !stop(a.outputF(nextProduced))
    ensures InvokeUntilTerminationMetric(a, input, stop) < old(InvokeUntilTerminationMetric(a, input, stop))
  {
    // var before := old(a.Produced());
    // var n: nat :| n <= |before| && Terminated(before, None, n);
    // var m: nat :| Terminated(a.Produced(), None, m);
    // if n < |before| {
    //   assert before[|before| - 1] == None;
    //   assert a.Produced()[|a.Produced()| - 1] != None;
    //   assert |a.Produced()| <= m;
    //   assert a.Produced()[|before| - 1] != None;
    //   assert false;
    // }
    // assert |before| <= n;
    
    // TerminatedDefinesEnumerated(before, n);
    // assert |Enumerated(before)| <= n;
    // TerminatedDistributesOverConcat(before, [nextProduced], None, 1);
    // assert Terminated(a.Produced(), None, |a.Produced()|);
    // TerminatedDefinesEnumerated(a.Produced(), |a.Produced()|);
  }

  // Enumerators

  type IEnumerator<T, TV(!new)> = Action<(), (), T, TV>
  type Enumerator<T, TV(!new)> = a: Action<(), (), Option<T>, Option<TV>> | IsEnumerator(a) witness *
  
  // Aggregators

  // TODO: Names need improvement
  type IAggregator<T, TV(!new)> = Action<T, TV, (), ()>
  type Aggregator<T, TV(!new)> = a: Action<T, TV, bool, bool> | exists limit: nat :: ProducesTerminatedBy(a, r => !r, limit) witness *
  type Accumulator<T, TV(!new)> = Action<Option<T>, Option<TV>, (), ()> // | exists limit :: ConsumesTerminatedBy(a, None, limit) witness *

  // Streams

  // BETTER IDEA!!!
  // 
  // RepeatUntil(t: T, stop: R) returns (Action<(), ()>)
  //   - invokes 1 or more times until stop is returned
  //   - requires CanConsume(<(t, !stop)*>, t)
  //   - NOT stopFn: R -> bool because then externs can't specialize
  //     - BUT instead: Compose(e, Compose(a, Function(stopFn))).RepeatUntil(t, true)
  // 
  // ForEach(e: Action<(), Option<T>>, a: Action<Option<T>, bool>)
  //   = Compose(e, a).RepeatUntil((), false)

  trait Stream<T, TV(!new)> extends Action<(), (), Option<T>, Option<TV>> {

    // A Stream is just a specialization of an Enumerator
    // with the potentially-optimized ForEach().
    // All implementors have to provide a body for this lemma
    // to prove they are in fact enumerators.
    // (think of this like `extends Enumerator<T>` which you can't actually say)
    lemma IsEnumerator()
      ensures (this as object) is Enumerator<T, TV>

    // Pass every value in sequence into the given accumulator.
    // Equivalent to DefaultForEach below,
    // but may be implemented more efficiently with concurrent execution
    // in the target language.
    method ForEach(a: Accumulator<T, TV>)
      requires Valid()
      requires a.Valid()
      requires Repr !! a.Repr 
      // The stream has produced all values
      // TODO: Needs to be more precise about producing exactly one None.
      // Something like EnumeratorDone(this)
      ensures 0 < |Produced()| && Seq.Last(Produced()) == None
      // Each value was fed into the accumulator in sequence
      ensures Produced() == a.Consumed()

    
  }

  class ArrayAggregator<T, TV(!new)> extends Action<T, TV, (), ()> {

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
      && Consumed() == Seq.Map(inputF, storage.items)
    }

    constructor(inputF: T -> TV) 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
      ensures this.inputF == inputF
      ensures this.outputF == (nothing => ())
    {
      var a := new DynamicArray();

      history := [];
      height := 1;
      Repr := {this} + {a} + a.Repr;
      this.storage := a;
      this.inputF := inputF;
      this.outputF := nothing => ();
    }

    ghost predicate CanConsume(history: seq<(TV, ())>, next: TV)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(TV, ())>)
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
      assert Consumed() == Seq.Map(inputF, storage.items);
      storage.Push(t);

      r := ();
      Update(t, r);
      Repr := {this} + {storage} + storage.Repr;
      assert Consumed() == old(Consumed()) + [inputF(t)];
      assert Valid();
    }

    method RepeatUntil(t: T, stop: (()) -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }
  }

  method {:rlimit 0} AggregatorExample() {
    var a: ArrayAggregator<nat, nat> := new ArrayAggregator((i: nat) => i);
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    var _ := a.Invoke(6);
    assert a.Consumed() == [1, 2, 3, 4, 5, 6];
    assert a.storage.items == [1, 2, 3, 4, 5, 6];
  }

  class FunctionalEnumerator<S, T, TV(!new)> extends Action<(), (), Option<T>, Option<TV>> {

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

    ghost predicate CanConsume(history: seq<((), Option<TV>)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<((), Option<TV>)>)
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

    method RepeatUntil(t: (), stop: Option<TV> -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }
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

  class BoxEnumerator extends Action<(), (), Box, nat> {

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
      && inputF == (i => i)
      && outputF == ((b: Box) => b.i)
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
      inputF := (i => i);
      outputF := ((b: Box) => b.i);
    }

    ghost predicate CanConsume(history: seq<((), nat)>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<((), nat)>)
      decreases height
    {
      Outputs(history) == SeqRange(|history|)
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

      SeqRangeIncr(producedBefore, |producedBefore|);
      assert Valid();
    }

    method RepeatUntil(t: (), stop: nat -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }
  }

  method {:rlimit 0} BoxEnumeratorExample() {
    var enum: BoxEnumerator := new BoxEnumerator();
    assert |enum.Produced()| == 0;
    var a := enum.Invoke(());

    assert enum.Produced() == [enum.outputF(a)];
    assert enum.Produced() == SeqRange(1) == [0];
    assert a.i == 0;
    
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


  class SeqEnumerator<T, TV(!new)> extends Action<(), (), Option<T>, Option<TV>> {

    var values: seq<T>

    constructor(values: seq<T>) {
      this.values := values;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr
    }
    
    ghost predicate CanConsume(history: seq<((), Option<TV>)>, next: ())
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<((), Option<TV>)>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(input: ()) returns (value: Option<T>) 
      modifies Repr
    {
      if |values| == 0 {
        value := None;
      } else {
        value := Some(values[0]);
        values := values[1..];
      }
    }

    method RepeatUntil(t: (), stop: Option<TV> -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }

  }

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
  class Collector<T, TV(!new)> extends Action<Option<T>, Option<TV>, (), ()> {

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

    ghost predicate CanConsume(history: seq<(Option<TV>, ())>, next: Option<TV>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(Option<TV>, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(t: Option<T>) returns (nothing: ()) {
      if t.Some? {
        values := values + [t.value];
      }
    }

    method RepeatUntil(t: Option<T>, stop: (()) -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }

    method {:verify false} Pop() returns (t: T) 
      requires 0 < |values|
    {
      t := values[0];
      values := values[1..];
    }

  }

  trait {:termination false} Pipeline<U, UV(!new), T, TV(!new)> extends Stream<T, TV> {
    

    const upstream: Stream<U, UV>
    const buffer: Collector<T, TV>

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

    method {:verify false} ForEach(a: Accumulator<T, TV>)
    {
      var a' := new PipelineProcessor(this, a);
      upstream.ForEach(a');
    }

    method Process(u: Option<U>, a: Accumulator<T, TV>)

  }

  class PipelineProcessor<U, UV(!new), T, TV(!new)> extends Action<Option<U>, Option<UV>, (), ()> {

    const pipeline: Pipeline<U, UV, T, TV>
    const accumulator: Accumulator<T, TV>

    constructor(pipeline: Pipeline<U, UV, T, TV>, accumulator: Accumulator<T, TV>) {
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

    ghost predicate CanConsume(history: seq<(Option<UV>, ())>, next: Option<UV>)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(Option<UV>, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(u: Option<U>) returns (nothing: ()) {
      pipeline.Process(u, accumulator);
    }

    method RepeatUntil(t: Option<U>, stop: (()) -> bool)
      requires Valid()
      requires EventuallyStops(this, t, stop)
      reads Reads(t)
      modifies Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop);
    }
  }
}