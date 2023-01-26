// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.10.0.41215
// Command Line Options: -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -runAllTests:1 -compile:0 -optimizeErasableDatatypeWrapper:0 -useRuntimeLib -out runtimes/net/ImplementationFromDafny ./src/Index.dfy -library:../DafnyLib/std/src/Index.dfy
// the_program


module {:extern ""Dafny.Simple.Aggregate""} SimpleAggregate refines AbstractSimpleAggregateService {

  import Operations = SimpleAggregateImpl
  class SimpleAggregateClient ...  {
    predicate ValidState()
      ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}
    {
      Operations.ValidInternalConfig?(config) &&
      Modifies == Operations.ModifiesInternalConfig(config) + {History}
    }

    constructor (config: Operations.InternalConfig)
      requires Operations.ValidInternalConfig?(config)
      ensures ValidState() && fresh(History) && this.config == config
      decreases config
    {
      this.config := config;
      History := new ISimpleAggregateClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

    const config: Operations.InternalConfig

    predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
      decreases input, output
    {
      Operations.GetAggregateEnsuresPublicly(input, output)
    }

    method GetAggregate(input: GetAggregateInput) returns (output: Result<GetAggregateOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetAggregate
      ensures true && ValidState()
      ensures GetAggregateEnsuresPublicly(input, output)
      ensures History.GetAggregate == old(History.GetAggregate) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GetAggregate(config, input);
      History.GetAggregate := History.GetAggregate + [DafnyCallEvent(input, output)];
    }
  }

  function method DefaultSimpleAggregateConfig(): SimpleAggregateConfig
  {
    SimpleAggregateConfig
  }

  method SimpleAggregate(config: SimpleAggregateConfig := DefaultSimpleAggregateConfig()) returns (res: Result<SimpleAggregateClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
  {
    var client := new SimpleAggregateClient(Operations.Config);
    return Success(client);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = SimpleAggregateTypes
}
method {:verify false} Main()

module StandardLibrary {

  import opened Wrappers

  import opened U = UInt
  lemma SeqTakeAppend<A>(s: seq<A>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i + 1]
    decreases s, i
  {
  }

  function method {:tailrecursion} Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method {:tailrecursion} Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    if i.Some? then
      [s[..i.value]] + Split(s[i.value + 1..], delim)
    else
      [s]
  }

  function method {:tailrecursion} SplitOnce<T(==)>(s: seq<T>, delim: T): (res: (seq<T>, seq<T>))
    requires delim in s
    ensures res.0 + [delim] + res.1 == s
    ensures !(delim in res.0)
    decreases s
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    assert i.Some?;
    (s[..i.value], s[i.value + 1..])
  }

  function method {:tailrecursion} SplitOnce?<T(==)>(s: seq<T>, delim: T): (res: Option<(seq<T>, seq<T>)>)
    ensures res.Some? ==> res.value.0 + [delim] + res.value.1 == s
    ensures res.None? ==> !(delim in s)
    ensures res.Some? ==> !(delim in res.value.0)
    decreases s
  {
    var i: nat :- FindIndexMatching(s, delim, 0); Some((s[..i], s[i + 1..]))
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i: int :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
    decreases s, prefix
  {
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
  }

  lemma FindIndexMatchingLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i: int :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures FindIndexMatching(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
  {
  }

  function method FindIndexMatching<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && s[index.value] == c && c !in s[i .. index.value]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    FindIndex(s, (x: T) => x == c, i)
  }

  function method {:tailrecursion} FindIndex<T>(s: seq<T>, f: T -> bool, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && f(s[index.value]) && forall j: int :: i <= j < index.value ==> !f(s[j])
    ensures index.None? ==> forall j: int :: i <= j < |s| ==> !f(s[j])
    decreases |s| - i
  {
    if i == |s| then
      None
    else if f(s[i]) then
      Some(i)
    else
      FindIndex(s, f, i + 1)
  }

  function method {:tailrecursion} Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int :: 0 <= i < |res| ==> res[i] in s && f(res[i])
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
  }

  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
    decreases s, i
  {
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    (forall x: T, y: T :: 
      less(x, y) || x == y || less(y, x)) &&
    (forall x: T, y: T :: 
      less(x, y) &&
      less(y, x) ==>
        false) &&
    forall x: T, y: T :: 
      less(x, y) ==>
        x != y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LexicographicLessOrEqual(a, a, less)
    decreases a
  {
  }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, a, less)
    ensures a == b
    decreases a, b
  {
  }

  lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, c, less)
    ensures LexicographicLessOrEqual(a, c, less)
    decreases a, b, c
  {
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
  }

  function method {:tailrecursion} SetToOrderedSequence<T(==,!new)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i: int :: 0 <= i < |q| ==> q[i] in s
    ensures forall k: seq<T> :: k in s ==> k in q
    ensures forall i: int :: 0 < i < |q| ==> LexicographicLessOrEqual(q[i - 1], q[i], less)
    ensures forall i: int, j: int | 0 <= i < j < |q| :: q[i] != q[j]
    decreases s
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s, less); assert forall a: seq<T>, b: seq<T> :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
    forall a: seq<T>, b: seq<T> | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
      MinimumIsUnique(a, b, s, less);
    }
  } var a: seq<T> :| a in s && IsMinimum(a, s, less); [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    decreases a, s
  {
    a in s &&
    forall z: seq<T> :: 
      z in s ==>
        LexicographicLessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a: seq<T> :: IsMinimum(a, s, less)
    decreases s
  {
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
    decreases a, b, s
  {
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
    decreases s
  {
  }

  module UInt {
    newtype uint8 = x: int
      | 0 <= x < 256

    newtype uint16 = x: int
      | 0 <= x < 65536

    newtype uint32 = x: int
      | 0 <= x < 4294967296

    newtype uint64 = x: int
      | 0 <= x < 18446744073709551616

    newtype int32 = x: int
      | -2147483648 <= x < 2147483648

    newtype int64 = x: int
      | -9223372036854775808 <= x < 9223372036854775808

    newtype posInt64 = x: int
      | 0 < x < 9223372036854775808
      witness 1

    type seq16<T> = s: seq<T>
      | HasUint16Len(s)

    type Uint8Seq16 = seq16<uint8>

    type seq32<T> = s: seq<T>
      | HasUint32Len(s)

    type Uint8Seq32 = seq32<uint8>

    type seq64<T> = s: seq<T>
      | HasUint64Len(s)

    type Uint8Seq64 = seq64<uint8>

    const UINT16_LIMIT := 65536
    const UINT32_LIMIT := 4294967296
    const UINT64_LIMIT := 18446744073709551616
    const INT32_MAX_LIMIT := 2147483648
    const INT64_MAX_LIMIT := 9223372036854775808

    predicate method UInt8Less(a: uint8, b: uint8)
      decreases a, b
    {
      a < b
    }

    predicate method HasUint16Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT16_LIMIT
    }

    predicate method HasUint32Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT32_LIMIT
    }

    predicate method HasUint64Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT64_LIMIT
    }

    function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
      ensures |ret| == 2
      ensures 256 * ret[0] as uint16 + ret[1] as uint16 == x
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): (x: uint16)
      requires |s| == 2
      ensures UInt16ToSeq(x) == s
      ensures x >= 0
      decreases s
    {
      var x0: uint16 := s[0] as uint16 * 256;
      x0 + s[1] as uint16
    }

    lemma UInt16SeqSerializeDeserialize(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
      ensures |ret| == 4
      ensures 16777216 * ret[0] as uint32 + 65536 * ret[1] as uint32 + 256 * ret[2] as uint32 + ret[3] as uint32 == x
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): (x: uint32)
      requires |s| == 4
      ensures UInt32ToSeq(x) == s
      decreases s
    {
      var x0: uint32 := s[0] as uint32 * 16777216;
      var x1: uint32 := x0 + s[1] as uint32 * 65536;
      var x2: uint32 := x1 + s[2] as uint32 * 256;
      x2 + s[3] as uint32
    }

    lemma UInt32SeqSerializeDeserialize(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
      ensures |ret| == 8
      ensures 72057594037927936 * ret[0] as uint64 + 281474976710656 * ret[1] as uint64 + 1099511627776 * ret[2] as uint64 + 4294967296 * ret[3] as uint64 + 16777216 * ret[4] as uint64 + 65536 * ret[5] as uint64 + 256 * ret[6] as uint64 + ret[7] as uint64 == x
      decreases x
    {
      var b0: uint8 := (x / 72057594037927936) as uint8;
      var x0: uint64 := x - b0 as uint64 * 72057594037927936;
      var b1: uint8 := (x0 / 281474976710656) as uint8;
      var x1: uint64 := x0 - b1 as uint64 * 281474976710656;
      var b2: uint8 := (x1 / 1099511627776) as uint8;
      var x2: uint64 := x1 - b2 as uint64 * 1099511627776;
      var b3: uint8 := (x2 / 4294967296) as uint8;
      var x3: uint64 := x2 - b3 as uint64 * 4294967296;
      var b4: uint8 := (x3 / 16777216) as uint8;
      var x4: uint64 := x3 - b4 as uint64 * 16777216;
      var b5: uint8 := (x4 / 65536) as uint8;
      var x5: uint64 := x4 - b5 as uint64 * 65536;
      var b6: uint8 := (x5 / 256) as uint8;
      var b7: uint8 := (x5 % 256) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method SeqToUInt64(s: seq<uint8>): (x: uint64)
      requires |s| == 8
      ensures UInt64ToSeq(x) == s
      decreases s
    {
      var x0: uint64 := s[0] as uint64 * 72057594037927936;
      var x1: uint64 := x0 + s[1] as uint64 * 281474976710656;
      var x2: uint64 := x1 + s[2] as uint64 * 1099511627776;
      var x3: uint64 := x2 + s[3] as uint64 * 4294967296;
      var x4: uint64 := x3 + s[4] as uint64 * 16777216;
      var x5: uint64 := x4 + s[5] as uint64 * 65536;
      var x6: uint64 := x5 + s[6] as uint64 * 256;
      var x: uint64 := x6 + s[7] as uint64;
      UInt64SeqSerialize(x, s);
      x
    }

    lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
      requires |s| == 8
      requires 72057594037927936 * s[0] as uint64 + 281474976710656 * s[1] as uint64 + 1099511627776 * s[2] as uint64 + 4294967296 * s[3] as uint64 + 16777216 * s[4] as uint64 + 65536 * s[5] as uint64 + 256 * s[6] as uint64 + s[7] as uint64 == x
      ensures UInt64ToSeq(x) == s
      decreases x, s
    {
    }

    lemma UInt64SeqSerializeDeserialize(x: uint64)
      ensures SeqToUInt64(UInt64ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 8
      ensures UInt64ToSeq(SeqToUInt64(s)) == s
      decreases s
    {
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        ghost var finalIndex: int := |s| - 1; SeqToNat(s[..finalIndex]) * 256 + s[finalIndex] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires ghost var suffixStartIndex: int := |s| - 4; s[suffixStartIndex..] == UInt32ToSeq(n as uint32) && forall i: int :: 0 <= i < suffixStartIndex ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
    }
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module {:extern ""UTF8""} UTF8 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  function method {:extern ""Encode""} Encode(s: string): (res: Result<ValidUTF8Bytes, string>)
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|
    ensures res.Success? ==> Decode(res.value).Success? && Decode(res.value).value == s
    decreases s

  function method {:extern ""Decode""} Decode(b: seq<uint8>): (res: Result<string, string>)
    ensures res.Success? ==> ValidUTF8Seq(b)
    decreases b

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  function method {:opaque} {:tailrecursion} {:fuel 0, 0} EncodeAscii(s: string): (ret: ValidUTF8Bytes)
    requires IsASCIIString(s)
    ensures |s| == |ret|
    ensures forall i: int | 0 <= i < |s| :: s[i] as uint8 == ret[i]
    decreases s
  {
    if |s| == 0 then
      []
    else
      var x: seq<uint8> := [s[0] as uint8]; assert ValidUTF8Seq(x); ValidUTF8Concat(x, EncodeAscii(s[1..])); x + EncodeAscii(s[1..])
  }

  lemma /*{:_induction x, y}*/ EncodeAsciiUnique2(x: string, y: string)
    requires IsASCIIString(x) && IsASCIIString(y)
    requires x != y
    ensures EncodeAscii(x) != EncodeAscii(y)
    decreases x, y
  {
  }

  lemma {:opaque} EncodeAsciiUnique()
    ensures forall x: string, y: string :: IsASCIIString(x) && IsASCIIString(y) && x != y ==> EncodeAscii(x) != EncodeAscii(y)
  {
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
    decreases s
  {
    0 <= s[0] <= 127
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
    decreases s
  {
    194 <= s[0] <= 223 &&
    128 <= s[1] <= 191
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
    decreases s
  {
    (s[0] == 224 && 160 <= s[1] <= 191 && 128 <= s[2] <= 191) || (225 <= s[0] <= 236 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191) || (s[0] == 237 && 128 <= s[1] <= 159 && 128 <= s[2] <= 191) || (238 <= s[0] <= 239 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191)
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
    decreases s
  {
    (s[0] == 240 && 144 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (241 <= s[0] <= 243 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (s[0] == 244 && 128 <= s[1] <= 143 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191)
  }

  predicate method {:tailrecursion} ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r: seq<uint8> := a[lo .. hi]; if Uses1Byte(r) then ValidUTF8Range(a, lo + 1, hi) else if 2 <= |r| && Uses2Bytes(r) then ValidUTF8Range(a, lo + 2, hi) else if 3 <= |r| && Uses3Bytes(r) then ValidUTF8Range(a, lo + 3, hi) else if 4 <= |r| && Uses4Bytes(r) then ValidUTF8Range(a, lo + 4, hi) else false
  }

  lemma /*{:_induction a, b, c, lo, hi}*/ ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
    decreases s, t
  {
  }
}

module SimpleAggregateImpl refines AbstractSimpleAggregateOperations {
  datatype Config = Config

  type InternalConfig = Config

  predicate ValidInternalConfig?(config: InternalConfig)
    decreases config
  {
    true
  }

  function ModifiesInternalConfig(config: InternalConfig): set<object>
    decreases config
  {
    {}
  }

  predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
    decreases input, output
  {
    true
  }

  method GetAggregate(config: InternalConfig, input: GetAggregateInput) returns (output: Result<GetAggregateOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetAggregateEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    var res := GetAggregateOutput(simpleStringList := input.simpleStringList, structureList := input.structureList, SimpleStringMap := input.SimpleStringMap, SimpleIntegerMap := input.SimpleIntegerMap, very := input.very);
    return Success(res);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = SimpleAggregateTypes
}

module {:extern ""Dafny.Simple.Aggregate.Types""} SimpleAggregateTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  datatype Deeply = Deeply(nameonly nested: Option<Nested>)

  datatype GetAggregateInput = GetAggregateInput(nameonly simpleStringList: Option<SimpleStringList>, nameonly structureList: Option<StructureList>, nameonly SimpleStringMap: Option<SimpleStringMap>, nameonly SimpleIntegerMap: Option<SimpleIntegerMap>, nameonly very: Option<Deeply>)

  datatype GetAggregateOutput = GetAggregateOutput(nameonly simpleStringList: Option<SimpleStringList>, nameonly structureList: Option<StructureList>, nameonly SimpleStringMap: Option<SimpleStringMap>, nameonly SimpleIntegerMap: Option<SimpleIntegerMap>, nameonly very: Option<Deeply>)

  datatype Nested = Nested(nameonly value: Option<string>)

  class ISimpleAggregateClientCallHistory {
    ghost constructor ()
    {
      GetAggregate := [];
    }

    ghost var GetAggregate: seq<DafnyCallEvent<GetAggregateInput, Result<GetAggregateOutput, Error>>>
  }

  trait {:termination false} ISimpleAggregateClient {
    ghost const Modifies: set<object>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies

    ghost const History: ISimpleAggregateClientCallHistory

    predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
      decreases input, output

    method GetAggregate(input: GetAggregateInput) returns (output: Result<GetAggregateOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetAggregate
      ensures true && ValidState()
      ensures GetAggregateEnsuresPublicly(input, output)
      ensures History.GetAggregate == old(History.GetAggregate) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
  }

  datatype SimpleAggregateConfig = SimpleAggregateConfig

  type SimpleIntegerMap = map<string, int32>

  type SimpleStringList = seq<string>

  type SimpleStringMap = map<string, string>

  type StructureList = seq<StructureListElement>

  datatype StructureListElement = StructureListElement(nameonly s: Option<string>, nameonly i: Option<int32>)

  datatype Error = Collection(list: seq<Error>) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *
}

abstract module AbstractSimpleAggregateService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = SimpleAggregateTypes

  import Operations : AbstractSimpleAggregateOperations
  class SimpleAggregateClient extends ISimpleAggregateClient {
    constructor (config: Operations.InternalConfig)
      requires Operations.ValidInternalConfig?(config)
      ensures ValidState() && fresh(History) && this.config == config

    const config: Operations.InternalConfig

    predicate ValidState()
      ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}

    predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
      decreases input, output
    {
      Operations.GetAggregateEnsuresPublicly(input, output)
    }

    method GetAggregate(input: GetAggregateInput) returns (output: Result<GetAggregateOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetAggregate
      ensures true && ValidState()
      ensures GetAggregateEnsuresPublicly(input, output)
      ensures History.GetAggregate == old(History.GetAggregate) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GetAggregate(config, input);
      History.GetAggregate := History.GetAggregate + [DafnyCallEvent(input, output)];
    }
  }

  function method DefaultSimpleAggregateConfig(): SimpleAggregateConfig

  method SimpleAggregate(config: SimpleAggregateConfig := DefaultSimpleAggregateConfig()) returns (res: Result<SimpleAggregateClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
}

abstract module AbstractSimpleAggregateOperations {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = SimpleAggregateTypes
  type InternalConfig

  predicate ValidInternalConfig?(config: InternalConfig)

  function ModifiesInternalConfig(config: InternalConfig): set<object>

  predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
    decreases input, output

  method GetAggregate(config: InternalConfig, input: GetAggregateInput) returns (output: Result<GetAggregateOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetAggregateEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Dafny.Simple.Aggregate.Types {

  public interface _IDafnyCallEvent<I, O> {
    bool is_DafnyCallEvent { get; }
    I dtor_input { get; }
    O dtor_output { get; }
    _IDafnyCallEvent<__I, __O> DowncastClone<__I, __O>(Func<I, __I> converter0, Func<O, __O> converter1);
  }
  public class DafnyCallEvent<I, O> : _IDafnyCallEvent<I, O> {
    public readonly I _input;
    public readonly O _output;
    public DafnyCallEvent(I input, O output) {
      this._input = input;
      this._output = output;
    }
    public _IDafnyCallEvent<__I, __O> DowncastClone<__I, __O>(Func<I, __I> converter0, Func<O, __O> converter1) {
      if (this is _IDafnyCallEvent<__I, __O> dt) { return dt; }
      return new DafnyCallEvent<__I, __O>(converter0(_input), converter1(_output));
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.DafnyCallEvent<I, O>;
      return oth != null && object.Equals(this._input, oth._input) && object.Equals(this._output, oth._output);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._output));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.DafnyCallEvent.DafnyCallEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static Dafny.Simple.Aggregate.Types._IDafnyCallEvent<I, O> Default(I _default_I, O _default_O) {
      return create(_default_I, _default_O);
    }
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IDafnyCallEvent<I, O>> _TypeDescriptor(Dafny.TypeDescriptor<I> _td_I, Dafny.TypeDescriptor<O> _td_O) {
      return new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IDafnyCallEvent<I, O>>(Dafny.Simple.Aggregate.Types.DafnyCallEvent<I, O>.Default(_td_I.Default(), _td_O.Default()));
    }
    public static _IDafnyCallEvent<I, O> create(I input, O output) {
      return new DafnyCallEvent<I, O>(input, output);
    }
    public bool is_DafnyCallEvent { get { return true; } }
    public I dtor_input {
      get {
        return this._input;
      }
    }
    public O dtor_output {
      get {
        return this._output;
      }
    }
  }

  public interface _IDeeply {
    bool is_Deeply { get; }
    Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> dtor_nested { get; }
    _IDeeply DowncastClone();
  }
  public class Deeply : _IDeeply {
    public readonly Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> _nested;
    public Deeply(Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> nested) {
      this._nested = nested;
    }
    public _IDeeply DowncastClone() {
      if (this is _IDeeply dt) { return dt; }
      return new Deeply(_nested);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.Deeply;
      return oth != null && object.Equals(this._nested, oth._nested);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nested));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.Deeply.Deeply";
      s += "(";
      s += Dafny.Helpers.ToString(this._nested);
      s += ")";
      return s;
    }
    private static readonly Dafny.Simple.Aggregate.Types._IDeeply theDefault = create(Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._INested>.Default());
    public static Dafny.Simple.Aggregate.Types._IDeeply Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IDeeply> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IDeeply>(Dafny.Simple.Aggregate.Types.Deeply.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IDeeply> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeeply create(Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> nested) {
      return new Deeply(nested);
    }
    public bool is_Deeply { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._INested> dtor_nested {
      get {
        return this._nested;
      }
    }
  }

  public interface _IGetAggregateInput {
    bool is_GetAggregateInput { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_simpleStringList { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> dtor_structureList { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SimpleStringMap { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> dtor_SimpleIntegerMap { get; }
    Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> dtor_very { get; }
    _IGetAggregateInput DowncastClone();
  }
  public class GetAggregateInput : _IGetAggregateInput {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _simpleStringList;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> _structureList;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _SimpleStringMap;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> _SimpleIntegerMap;
    public readonly Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> _very;
    public GetAggregateInput(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> simpleStringList, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> structureList, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SimpleStringMap, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> SimpleIntegerMap, Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> very) {
      this._simpleStringList = simpleStringList;
      this._structureList = structureList;
      this._SimpleStringMap = SimpleStringMap;
      this._SimpleIntegerMap = SimpleIntegerMap;
      this._very = very;
    }
    public _IGetAggregateInput DowncastClone() {
      if (this is _IGetAggregateInput dt) { return dt; }
      return new GetAggregateInput(_simpleStringList, _structureList, _SimpleStringMap, _SimpleIntegerMap, _very);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.GetAggregateInput;
      return oth != null && object.Equals(this._simpleStringList, oth._simpleStringList) && object.Equals(this._structureList, oth._structureList) && object.Equals(this._SimpleStringMap, oth._SimpleStringMap) && object.Equals(this._SimpleIntegerMap, oth._SimpleIntegerMap) && object.Equals(this._very, oth._very);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._simpleStringList));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._structureList));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SimpleStringMap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SimpleIntegerMap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._very));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.GetAggregateInput.GetAggregateInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._simpleStringList);
      s += ", ";
      s += Dafny.Helpers.ToString(this._structureList);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SimpleStringMap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SimpleIntegerMap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._very);
      s += ")";
      return s;
    }
    private static readonly Dafny.Simple.Aggregate.Types._IGetAggregateInput theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,int>>.Default(), Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.Default());
    public static Dafny.Simple.Aggregate.Types._IGetAggregateInput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateInput> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateInput>(Dafny.Simple.Aggregate.Types.GetAggregateInput.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateInput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetAggregateInput create(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> simpleStringList, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> structureList, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SimpleStringMap, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> SimpleIntegerMap, Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> very) {
      return new GetAggregateInput(simpleStringList, structureList, SimpleStringMap, SimpleIntegerMap, very);
    }
    public bool is_GetAggregateInput { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_simpleStringList {
      get {
        return this._simpleStringList;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> dtor_structureList {
      get {
        return this._structureList;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SimpleStringMap {
      get {
        return this._SimpleStringMap;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> dtor_SimpleIntegerMap {
      get {
        return this._SimpleIntegerMap;
      }
    }
    public Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> dtor_very {
      get {
        return this._very;
      }
    }
  }

  public interface _IGetAggregateOutput {
    bool is_GetAggregateOutput { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_simpleStringList { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> dtor_structureList { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SimpleStringMap { get; }
    Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> dtor_SimpleIntegerMap { get; }
    Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> dtor_very { get; }
    _IGetAggregateOutput DowncastClone();
  }
  public class GetAggregateOutput : _IGetAggregateOutput {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> _simpleStringList;
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> _structureList;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> _SimpleStringMap;
    public readonly Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> _SimpleIntegerMap;
    public readonly Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> _very;
    public GetAggregateOutput(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> simpleStringList, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> structureList, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SimpleStringMap, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> SimpleIntegerMap, Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> very) {
      this._simpleStringList = simpleStringList;
      this._structureList = structureList;
      this._SimpleStringMap = SimpleStringMap;
      this._SimpleIntegerMap = SimpleIntegerMap;
      this._very = very;
    }
    public _IGetAggregateOutput DowncastClone() {
      if (this is _IGetAggregateOutput dt) { return dt; }
      return new GetAggregateOutput(_simpleStringList, _structureList, _SimpleStringMap, _SimpleIntegerMap, _very);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.GetAggregateOutput;
      return oth != null && object.Equals(this._simpleStringList, oth._simpleStringList) && object.Equals(this._structureList, oth._structureList) && object.Equals(this._SimpleStringMap, oth._SimpleStringMap) && object.Equals(this._SimpleIntegerMap, oth._SimpleIntegerMap) && object.Equals(this._very, oth._very);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._simpleStringList));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._structureList));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SimpleStringMap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._SimpleIntegerMap));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._very));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.GetAggregateOutput.GetAggregateOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._simpleStringList);
      s += ", ";
      s += Dafny.Helpers.ToString(this._structureList);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SimpleStringMap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._SimpleIntegerMap);
      s += ", ";
      s += Dafny.Helpers.ToString(this._very);
      s += ")";
      return s;
    }
    private static readonly Dafny.Simple.Aggregate.Types._IGetAggregateOutput theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>>.Default(), Wrappers_Compile.Option<Dafny.IMap<Dafny.ISequence<char>,int>>.Default(), Wrappers_Compile.Option<Dafny.Simple.Aggregate.Types._IDeeply>.Default());
    public static Dafny.Simple.Aggregate.Types._IGetAggregateOutput Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateOutput> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateOutput>(Dafny.Simple.Aggregate.Types.GetAggregateOutput.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IGetAggregateOutput> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetAggregateOutput create(Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> simpleStringList, Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> structureList, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> SimpleStringMap, Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> SimpleIntegerMap, Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> very) {
      return new GetAggregateOutput(simpleStringList, structureList, SimpleStringMap, SimpleIntegerMap, very);
    }
    public bool is_GetAggregateOutput { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<char>>> dtor_simpleStringList {
      get {
        return this._simpleStringList;
      }
    }
    public Wrappers_Compile._IOption<Dafny.ISequence<Dafny.Simple.Aggregate.Types._IStructureListElement>> dtor_structureList {
      get {
        return this._structureList;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,Dafny.ISequence<char>>> dtor_SimpleStringMap {
      get {
        return this._SimpleStringMap;
      }
    }
    public Wrappers_Compile._IOption<Dafny.IMap<Dafny.ISequence<char>,int>> dtor_SimpleIntegerMap {
      get {
        return this._SimpleIntegerMap;
      }
    }
    public Wrappers_Compile._IOption<Dafny.Simple.Aggregate.Types._IDeeply> dtor_very {
      get {
        return this._very;
      }
    }
  }

  public interface _INested {
    bool is_Nested { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_value { get; }
    _INested DowncastClone();
  }
  public class Nested : _INested {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _value;
    public Nested(Wrappers_Compile._IOption<Dafny.ISequence<char>> @value) {
      this._value = @value;
    }
    public _INested DowncastClone() {
      if (this is _INested dt) { return dt; }
      return new Nested(_value);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.Nested;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.Nested.Nested";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
    private static readonly Dafny.Simple.Aggregate.Types._INested theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static Dafny.Simple.Aggregate.Types._INested Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._INested> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._INested>(Dafny.Simple.Aggregate.Types.Nested.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._INested> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INested create(Wrappers_Compile._IOption<Dafny.ISequence<char>> @value) {
      return new Nested(@value);
    }
    public bool is_Nested { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_value {
      get {
        return this._value;
      }
    }
  }

  public partial class ISimpleAggregateClientCallHistory {
    public ISimpleAggregateClientCallHistory() {
    }
  }

  public interface ISimpleAggregateClient {
    Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> GetAggregate(Dafny.Simple.Aggregate.Types._IGetAggregateInput input);
  }
  public class _Companion_ISimpleAggregateClient {
  }

  public interface _ISimpleAggregateConfig {
    bool is_SimpleAggregateConfig { get; }
    _ISimpleAggregateConfig DowncastClone();
  }
  public class SimpleAggregateConfig : _ISimpleAggregateConfig {
    public SimpleAggregateConfig() {
    }
    public _ISimpleAggregateConfig DowncastClone() {
      if (this is _ISimpleAggregateConfig dt) { return dt; }
      return new SimpleAggregateConfig();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.SimpleAggregateConfig;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.SimpleAggregateConfig.SimpleAggregateConfig";
      return s;
    }
    private static readonly Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig theDefault = create();
    public static Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig>(Dafny.Simple.Aggregate.Types.SimpleAggregateConfig.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISimpleAggregateConfig create() {
      return new SimpleAggregateConfig();
    }
    public bool is_SimpleAggregateConfig { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_ISimpleAggregateConfig> AllSingletonConstructors {
      get {
        yield return SimpleAggregateConfig.create();
      }
    }
  }

  public interface _IStructureListElement {
    bool is_StructureListElement { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_s { get; }
    Wrappers_Compile._IOption<int> dtor_i { get; }
    _IStructureListElement DowncastClone();
  }
  public class StructureListElement : _IStructureListElement {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _s;
    public readonly Wrappers_Compile._IOption<int> _i;
    public StructureListElement(Wrappers_Compile._IOption<Dafny.ISequence<char>> s, Wrappers_Compile._IOption<int> i) {
      this._s = s;
      this._i = i;
    }
    public _IStructureListElement DowncastClone() {
      if (this is _IStructureListElement dt) { return dt; }
      return new StructureListElement(_s, _i);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.StructureListElement;
      return oth != null && object.Equals(this._s, oth._s) && object.Equals(this._i, oth._i);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Dafny.Simple.Aggregate.Types_Compile.StructureListElement.StructureListElement";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._i);
      ss += ")";
      return ss;
    }
    private static readonly Dafny.Simple.Aggregate.Types._IStructureListElement theDefault = create(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default(), Wrappers_Compile.Option<int>.Default());
    public static Dafny.Simple.Aggregate.Types._IStructureListElement Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IStructureListElement> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IStructureListElement>(Dafny.Simple.Aggregate.Types.StructureListElement.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IStructureListElement> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStructureListElement create(Wrappers_Compile._IOption<Dafny.ISequence<char>> s, Wrappers_Compile._IOption<int> i) {
      return new StructureListElement(s, i);
    }
    public bool is_StructureListElement { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_s {
      get {
        return this._s;
      }
    }
    public Wrappers_Compile._IOption<int> dtor_i {
      get {
        return this._i;
      }
    }
  }

  public interface _IError {
    bool is_Collection { get; }
    bool is_Opaque { get; }
    Dafny.ISequence<Dafny.Simple.Aggregate.Types._IError> dtor_list { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly Dafny.Simple.Aggregate.Types._IError theDefault = create_Collection(Dafny.Sequence<Dafny.Simple.Aggregate.Types._IError>.Empty);
    public static Dafny.Simple.Aggregate.Types._IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError>(Dafny.Simple.Aggregate.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_Collection(Dafny.ISequence<Dafny.Simple.Aggregate.Types._IError> list) {
      return new Error_Collection(list);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_Collection { get { return this is Error_Collection; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Dafny.ISequence<Dafny.Simple.Aggregate.Types._IError> dtor_list {
      get {
        var d = this;
        return ((Error_Collection)d)._list;
      }
    }
    public object dtor_obj {
      get {
        var d = this;
        return ((Error_Opaque)d)._obj;
      }
    }
    public abstract _IError DowncastClone();
  }
  public class Error_Collection : Error {
    public readonly Dafny.ISequence<Dafny.Simple.Aggregate.Types._IError> _list;
    public Error_Collection(Dafny.ISequence<Dafny.Simple.Aggregate.Types._IError> list) {
      this._list = list;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Collection(_list);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.Error_Collection;
      return oth != null && object.Equals(this._list, oth._list);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._list));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.Error.Collection";
      s += "(";
      s += Dafny.Helpers.ToString(this._list);
      s += ")";
      return s;
    }
  }
  public class Error_Opaque : Error {
    public readonly object _obj;
    public Error_Opaque(object obj) {
      this._obj = obj;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Opaque(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Simple.Aggregate.Types.Error_Opaque;
      return oth != null && this._obj == oth._obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Simple.Aggregate.Types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError>(Dafny.Simple.Aggregate.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Simple.Aggregate.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace Dafny.Simple.Aggregate.Types
namespace SimpleAggregateImpl_Compile {

  public interface _IConfig {
    bool is_Config { get; }
    _IConfig DowncastClone();
  }
  public class Config : _IConfig {
    public Config() {
    }
    public _IConfig DowncastClone() {
      if (this is _IConfig dt) { return dt; }
      return new Config();
    }
    public override bool Equals(object other) {
      var oth = other as SimpleAggregateImpl_Compile.Config;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SimpleAggregateImpl_Compile.Config.Config";
      return s;
    }
    private static readonly SimpleAggregateImpl_Compile._IConfig theDefault = create();
    public static SimpleAggregateImpl_Compile._IConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<SimpleAggregateImpl_Compile._IConfig> _TYPE = new Dafny.TypeDescriptor<SimpleAggregateImpl_Compile._IConfig>(SimpleAggregateImpl_Compile.Config.Default());
    public static Dafny.TypeDescriptor<SimpleAggregateImpl_Compile._IConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConfig create() {
      return new Config();
    }
    public bool is_Config { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IConfig> AllSingletonConstructors {
      get {
        yield return Config.create();
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> GetAggregate(SimpleAggregateImpl_Compile._IConfig config, Dafny.Simple.Aggregate.Types._IGetAggregateInput input)
    {
      Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> output = Wrappers_Compile.Result<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError>.Default(Dafny.Simple.Aggregate.Types.GetAggregateOutput.Default());
      Dafny.Simple.Aggregate.Types._IGetAggregateOutput _0_res;
      _0_res = Dafny.Simple.Aggregate.Types.GetAggregateOutput.create((input).dtor_simpleStringList, (input).dtor_structureList, (input).dtor_SimpleStringMap, (input).dtor_SimpleIntegerMap, (input).dtor_very);
      output = Wrappers_Compile.Result<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError>.create_Success(_0_res);
      return output;
      return output;
    }
  }
} // end of namespace SimpleAggregateImpl_Compile
namespace Dafny.Simple.Aggregate {

  public partial class SimpleAggregateClient : Dafny.Simple.Aggregate.Types.ISimpleAggregateClient {
    public SimpleAggregateClient() {
      this._config = SimpleAggregateImpl_Compile.Config.Default();
    }
    public void __ctor(SimpleAggregateImpl_Compile._IConfig config)
    {
      (this)._config = config;
    }
    public Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> GetAggregate(Dafny.Simple.Aggregate.Types._IGetAggregateInput input)
    {
      Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> output = Wrappers_Compile.Result<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError>.Default(Dafny.Simple.Aggregate.Types.GetAggregateOutput.Default());
      Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> _out0;
      _out0 = SimpleAggregateImpl_Compile.__default.GetAggregate((this).config, input);
      output = _out0;
      return output;
    }
    public SimpleAggregateImpl_Compile._IConfig _config {get; set;}
    public SimpleAggregateImpl_Compile._IConfig config { get {
      return this._config;
    } }
  }

  public partial class __default {
    public static Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig DefaultSimpleAggregateConfig() {
      return Dafny.Simple.Aggregate.Types.SimpleAggregateConfig.create();
    }
    public static Wrappers_Compile._IResult<Dafny.Simple.Aggregate.SimpleAggregateClient, Dafny.Simple.Aggregate.Types._IError> SimpleAggregate(Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig config)
    {
      Wrappers_Compile._IResult<Dafny.Simple.Aggregate.SimpleAggregateClient, Dafny.Simple.Aggregate.Types._IError> res = default(Wrappers_Compile._IResult<Dafny.Simple.Aggregate.SimpleAggregateClient, Dafny.Simple.Aggregate.Types._IError>);
      Dafny.Simple.Aggregate.SimpleAggregateClient _1_client;
      Dafny.Simple.Aggregate.SimpleAggregateClient _nw0 = new Dafny.Simple.Aggregate.SimpleAggregateClient();
      _nw0.__ctor(SimpleAggregateImpl_Compile.Config.create());
      _1_client = _nw0;
      res = Wrappers_Compile.Result<Dafny.Simple.Aggregate.SimpleAggregateClient, Dafny.Simple.Aggregate.Types._IError>.create_Success(_1_client);
      return res;
      return res;
    }
  }
} // end of namespace Dafny.Simple.Aggregate
namespace _module {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      bool _2_success;
      _2_success = true;
      if (!(_2_success)) {
        throw new Dafny.HaltException("/Users/scchatur/workspace/polymorph/TestModels/Aggregate/src/Index.dfy(17,18): " + Dafny.Sequence<char>.FromString(@"Test failures occurred: see above.
"));
      }
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default._Main(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}
