
include "../../libraries/src/Wrappers.dfy"

include "Frames.dfy"
include "GenericAction.dfy"
include "DecreasesClauses.dfy"
include "DynamicArray.dfy"

module {:options "--function-syntax:4"} Std.Actions {

  import opened Wrappers
  import opened Frames
  import opened GenericActions
  import opened Termination
  import opened DynamicArray

  // TODO: Documentation, especially overall design
  trait {:termination false} Action<T, TV(!new), R, RV(!new)> extends GenericAction<T, R>, Validatable {

    ghost var history: seq<(TV, RV)>
    // TODO: Make these --> functions (not ~>, they are useless if they read the heap)
    ghost const inputF: T -> TV
    ghost const outputF: R -> RV

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


  // Dependencies stolen from DafnyStandardLibraries
  
  function {:opaque} SeqMap<T, R>(f: (T ~> R), xs: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then []
    else [f(xs[0])] + SeqMap(f, xs[1..])
  }

  /* Returns the last element of a non-empty sequence. */
  function SeqLast<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[|xs|-1]
  }

  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else a
  }

  // Common action invariants

  function Inputs<T, R>(history: seq<(T, R)>): seq<T> {
    SeqMap((e: (T, R)) => e.0, history)
  }

  function Outputs<T, R>(history: seq<(T, R)>): seq<R> {
    SeqMap((e: (T, R)) => e.1, history)
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

  ghost predicate Terminated<T>(s: seq<T>, c: T, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> s[i] == c
  }

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, c: T, n: nat)
    requires Terminated(left + right, c, n)
    ensures Terminated(left, c, n)
    ensures Terminated(right, c, Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  // TODO: generalize to "EventuallyProducesSequence"?
  ghost predicate ProducesTerminatedBy<T, TV(!new), R, RV(!new)>(i: Action<T, TV, R, RV>, c: RV, limit: nat) {
    forall history: seq<(TV, RV)> | i.CanProduce(history) 
      :: exists n: nat | n <= limit :: Terminated(Outputs(history), c, n)
  }

  // Class of actions whose precondition doesn't depend on history (probably needs a better name)
  ghost predicate ContextFree<T, TV(!new), R, RV(!new)>(a: Action<T, TV, R, RV>, p: TV -> bool) {
    forall history, next | a.CanProduce(history)
      :: a.CanConsume(history, next) <==> p(next)
  }

  // Enumerators

  type IEnumerator<T, TV(!new)> = Action<(), (), T, TV>
  type Enumerator<T, TV(!new)> = a: Action<(), (), Option<T>, Option<TV>> | exists limit :: ProducesTerminatedBy(a, None, limit) witness *
  

  // Aggregators

  // TODO: Names need improvement
  type IAggregator<T, TV(!new)> = Action<T, TV, (), ()>
  type Aggregator<T, TV(!new)> = a: Action<T, TV, bool, bool> | exists limit :: ProducesTerminatedBy(a, false, limit) witness *
  type Accumulator<T, TV(!new)> = Action<Option<T>, Option<TV>, (), ()> // | exists limit :: ConsumesTerminatedBy(a, None, limit) witness *

  // Streams

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
      ensures 0 < |Produced()| && SeqLast(Produced()) == None
      // Each value was fed into the accumulator in sequence
      ensures Produced() == a.Consumed()

    
  }

  method {:verify false} DefaultForEach<T, TV(!new)>(s: Enumerator<T, TV>, a: Accumulator<T, TV>) {
    // TODO: Actual specs to prove this terminates
    while (true) {
      var next := s.Invoke(());
      if next == None {
        break;
      }

      var _ := a.Invoke(next);
    }
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
      && Consumed() == SeqMap(inputF, storage.items)
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
      assert Consumed() == SeqMap(inputF, storage.items);
      storage.Push(t);

      r := ();
      Update(t, r);
      Repr := {this} + {storage} + storage.Repr;
      assert Consumed() == old(Consumed()) + [inputF(t)];
      assert Valid();
    }
  }

  method {:rlimit 0} AggregatorExample() {
    var a: ArrayAggregator<nat, nat> := new ArrayAggregator(i => i);
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    var _ := a.Invoke(6);
    assert a.Consumed() == [1, 2, 3, 4, 5, 6];
    assert a.storage.items == [1, 2, 3, 4, 5, 6];
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
  }
}