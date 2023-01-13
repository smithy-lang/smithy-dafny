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
// Command Line Options: -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -compile:0 -useRuntimeLib -out runtimes/net/ImplementationFromDafny ./src/Index.dfy -library:../smithy-polymorph/lib/std/src/Index.dfy
// the_program


module {:extern ""Dafny.Example.Simpletypes""} SimpleTypes refines AbstractExampleSimpletypesService {

  import Operations = SimpleTypesImpl
  class SimpleTypesClient ...  {
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
      History := new ISimpleTypesServiceClientCallHistory();
      Modifies := Operations.ModifiesInternalConfig(config) + {History};
    }

    const config: Operations.InternalConfig

    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
      decreases input, output
    {
      Operations.GetStringEnsuresPublicly(input, output)
    }

    method GetString(input: GetStringInput) returns (output: Result<GetStringOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetString
      ensures true && ValidState()
      ensures GetStringEnsuresPublicly(input, output)
      ensures History.GetString == old(History.GetString) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GetString(config, input);
      History.GetString := History.GetString + [DafnyCallEvent(input, output)];
    }
  }

  function method DefaultEmptyConfig(): EmptyConfig
  {
    EmptyConfig
  }

  method SimpleTypes(config: EmptyConfig := DefaultEmptyConfig()) returns (res: Result<SimpleTypesClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
  {
    var client := new SimpleTypesClient(Operations.Config);
    return Success(client);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ExampleSimpletypesTypes
}

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

  module String {

    export
      provides Int2String, Base10Int2String

    const Base10: seq<char> := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

    function method Int2Digits(n: int, base: int): (digits: seq<int>)
      requires base > 1
      requires n >= 0
      ensures forall d: int | d in digits :: 0 <= d < base
      decreases n
    {
      if n == 0 then
        []
      else
        assert n > 0; assert base > 1; assert n < base * n; assert n / base < n; Int2Digits(n / base, base) + [n % base]
    }

    function method Digits2String(digits: seq<int>, chars: seq<char>): string
      requires forall d: int | d in digits :: 0 <= d < |chars|
      decreases digits, chars
    {
      if digits == [] then
        """"
      else
        assert digits[0] in digits; assert forall d: int | d in digits[1..] :: d in digits; [chars[digits[0]]] + Digits2String(digits[1..], chars)
    }

    function method Int2String(n: int, chars: seq<char>): string
      requires |chars| > 1
      decreases n, chars
    {
      var base: int := |chars|;
      if n == 0 then
        ""0""
      else if n > 0 then
        Digits2String(Int2Digits(n, base), chars)
      else
        ""-"" + Digits2String(Int2Digits(-n, base), chars)
    }

    function method Base10Int2String(n: int): string
      decreases n
    {
      Int2String(n, Base10)
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

module Base64 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  newtype index = x: int
    | 0 <= x < 64

  newtype uint24 = x: int
    | 0 <= x < 16777216

  predicate method IsBase64Char(c: char)
    decreases c
  {
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  predicate method IsUnpaddedBase64String(s: string)
    decreases s
  {
    |s| % 4 == 0 &&
    forall k: char :: 
      k in s ==>
        IsBase64Char(k)
  }

  function method IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
    decreases i
  {
    if i == 63 then
      '/'
    else if i == 62 then
      '+'
    else if 52 <= i <= 61 then
      (i - 4) as char
    else if 26 <= i <= 51 then
      i as char + 71 as char
    else
      i as char + 65 as char
  }

  function method CharToIndex(c: char): (i: index)
    requires IsBase64Char(c)
    ensures IndexToChar(i) == c
    decreases c
  {
    if c == '/' then
      63
    else if c == '+' then
      62
    else if '0' <= c <= '9' then
      (c + 4 as char) as index
    else if 'a' <= c <= 'z' then
      (c - 71 as char) as index
    else
      (c - 65 as char) as index
  }

  lemma CharToIndexToChar(x: char)
    requires IsBase64Char(x)
    ensures IndexToChar(CharToIndex(x)) == x
    decreases x
  {
  }

  lemma IndexToCharToIndex(x: index)
    ensures CharToIndex(IndexToChar(x)) == x
    decreases x
  {
  }

  function method UInt24ToSeq(x: uint24): (ret: seq<uint8>)
    ensures |ret| == 3
    ensures ret[0] as uint24 * 65536 + ret[1] as uint24 * 256 + ret[2] as uint24 == x
    decreases x
  {
    var b0: uint8 := (x / 65536) as uint8;
    var x0: uint24 := x - b0 as uint24 * 65536;
    var b1: uint8 := (x0 / 256) as uint8;
    var b2: uint8 := (x0 % 256) as uint8;
    [b0, b1, b2]
  }

  function method SeqToUInt24(s: seq<uint8>): (x: uint24)
    requires |s| == 3
    ensures UInt24ToSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 65536 + s[1] as uint24 * 256 + s[2] as uint24
  }

  lemma UInt24ToSeqToUInt24(x: uint24)
    ensures SeqToUInt24(UInt24ToSeq(x)) == x
    decreases x
  {
  }

  lemma SeqToUInt24ToSeq(s: seq<uint8>)
    requires |s| == 3
    ensures UInt24ToSeq(SeqToUInt24(s)) == s
    decreases s
  {
  }

  function method UInt24ToIndexSeq(x: uint24): (ret: seq<index>)
    ensures |ret| == 4
    ensures ret[0] as uint24 * 262144 + ret[1] as uint24 * 4096 + ret[2] as uint24 * 64 + ret[3] as uint24 == x
    decreases x
  {
    var b0: index := (x / 262144) as index;
    var x0: uint24 := x - b0 as uint24 * 262144;
    var b1: index := (x0 / 4096) as index;
    var x1: uint24 := x0 - b1 as uint24 * 4096;
    var b2: index := (x1 / 64) as index;
    var b3: index := (x1 % 64) as index;
    [b0, b1, b2, b3]
  }

  function method IndexSeqToUInt24(s: seq<index>): (x: uint24)
    requires |s| == 4
    ensures UInt24ToIndexSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 262144 + s[1] as uint24 * 4096 + s[2] as uint24 * 64 + s[3] as uint24
  }

  lemma UInt24ToIndexSeqToUInt24(x: uint24)
    ensures IndexSeqToUInt24(UInt24ToIndexSeq(x)) == x
    decreases x
  {
  }

  lemma IndexSeqToUInt24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures UInt24ToIndexSeq(IndexSeqToUInt24(s)) == s
    decreases s
  {
  }

  function method DecodeBlock(s: seq<index>): (ret: seq<uint8>)
    requires |s| == 4
    ensures |ret| == 3
    ensures UInt24ToIndexSeq(SeqToUInt24(ret)) == s
    decreases s
  {
    UInt24ToSeq(IndexSeqToUInt24(s))
  }

  function method EncodeBlock(s: seq<uint8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
    ensures UInt24ToSeq(IndexSeqToUInt24(ret)) == s
    ensures DecodeBlock(ret) == s
    decreases s
  {
    UInt24ToIndexSeq(SeqToUInt24(s))
  }

  lemma EncodeDecodeBlock(s: seq<uint8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
    decreases s
  {
  }

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
    decreases s
  {
  }

  function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
    requires |s| % 4 == 0
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    ensures |b| == 0 ==> |s| == 0
    ensures |b| != 0 ==> EncodeBlock(b[..3]) == s[..4]
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  }

  function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
    ensures DecodeRecursively(s) == b
    decreases b
  {
    if |b| == 0 then
      []
    else
      EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  }

  lemma /*{:_induction s}*/ DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures EncodeRecursively(DecodeRecursively(s)) == s
    decreases s
  {
  }

  lemma /*{:_induction b}*/ EncodeDecodeRecursively(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeRecursively(EncodeRecursively(b)) == b
    decreases b
  {
  }

  function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k: char :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
    ensures forall k: int :: 0 <= k < |b| ==> IndexToChar(b[k]) == s[k]
    decreases s
  {
    seq(|s|, (i: int) requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k: char :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
    ensures forall k: int :: 0 <= k < |s| ==> CharToIndex(s[k]) == b[k]
    ensures FromCharsToIndices(s) == b
    decreases b
  {
    seq(|b|, (i: int) requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k: char :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
    decreases s
  {
  }

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
    decreases b
  {
  }

  function method DecodeUnpadded(s: seq<char>): (b: seq<uint8>)
    requires IsUnpaddedBase64String(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    decreases s
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method EncodeUnpadded(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeUnpadded(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeDecodeUnpadded(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeUnpadded(EncodeUnpadded(b)) == b
    decreases b
  {
  }

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedBase64String(s)
    ensures EncodeUnpadded(DecodeUnpadded(s)) == s
    decreases s
  {
  }

  predicate method Is1Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    CharToIndex(s[2]) % 4 == 0 &&
    s[3] == '='
  }

  function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
    requires Is1Padding(s)
    ensures |b| == 2
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  function method Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], b[1], 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']
  }

  lemma DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode1Padding(b: seq<uint8>)
    requires |b| == 2
    ensures Decode1Padding(Encode1Padding(b)) == b
    decreases b
  {
  }

  predicate method Is2Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    CharToIndex(s[1]) % 16 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
    requires Is2Padding(s)
    ensures |b| == 1
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], 0, 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']
  }

  lemma DecodeEncode2Padding(s: seq<char>)
    requires Is2Padding(s)
    ensures Encode2Padding(Decode2Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode2Padding(b: seq<uint8>)
    requires |b| == 1
    ensures Decode2Padding(Encode2Padding(b)) == b
    decreases b
  {
  }

  predicate method IsBase64String(s: string)
    decreases s
  {
    var finalBlockStart: int := |s| - 4;
    |s| % 4 == 0 &&
    (IsUnpaddedBase64String(s) || (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
    decreases s
  {
    if s == [] then
      []
    else
      var finalBlockStart: int := |s| - 4; var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; if Is1Padding(suffix) then DecodeUnpadded(prefix) + Decode1Padding(suffix) else if Is2Padding(suffix) then DecodeUnpadded(prefix) + Decode2Padding(suffix) else DecodeUnpadded(s)
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<uint8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> ghost var finalBlockStart: int := |s| - 4; ghost var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; (Is1Padding(suffix) ==> |b| % 3 == 2) && (Is2Padding(suffix) ==> |b| % 3 == 1) && (!Is1Padding(suffix) && !Is2Padding(suffix) ==> |b| % 3 == 0)
    decreases s, b
  {
  }

  lemma Mod3(x: nat, k: nat, n: nat)
    requires 0 <= k < 3 && n == 3 * x + k
    ensures n % 3 == k
    decreases x, k, n
  {
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>, string>)
    ensures IsBase64String(s) ==> b.Success?
    ensures !IsBase64String(s) ==> b.Failure?
    decreases s
  {
    if IsBase64String(s) then
      Success(DecodeValid(s))
    else
      Failure(""The encoding is malformed"")
  }

  predicate StringIs7Bit(s: string)
    decreases s
  {
    forall i: int :: 
      0 <= i < |s| ==>
        s[i] < 128 as char
  }

  lemma ConcatMod4Sequences<T>(s: seq<T>, t: seq<T>)
    requires |s| % 4 == 0
    requires |t| % 4 == 0
    ensures |s + t| % 4 == 0
    decreases s, t
  {
  }

  function method Encode(b: seq<uint8>): (s: seq<char>)
    ensures StringIs7Bit(s)
    ensures |s| % 4 == 0
    ensures IsBase64String(s)
    decreases b
  {
    if |b| % 3 == 0 then
      var s: seq<char> := EncodeUnpadded(b);
      assert |s| % 4 == 0;
      s
    else if |b| % 3 == 1 then
      assert |b| >= 1;
      var s1: seq<char>, s2: seq<char> := EncodeUnpadded(b[..|b| - 1]), Encode2Padding(b[|b| - 1..]);
      ConcatMod4Sequences(s1, s2);
      var s: seq<char> := s1 + s2;
      assert |s| % 4 == 0;
      s
    else
      assert |b| % 3 == 2; assert |b| >= 2; var s1: seq<char>, s2: seq<char> := EncodeUnpadded(b[..|b| - 2]), Encode1Padding(b[|b| - 2..]); ConcatMod4Sequences(s1, s2); var s: seq<char> := s1 + s2; assert |s| % 4 == 0; s
  }

  lemma EncodeLengthExact(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); (|b| % 3 == 0 ==> |s| == |b| / 3 * 4) && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
    decreases b
  {
  }

  lemma EncodeLengthBound(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); |s| <= |b| / 3 * 4 + 4
    decreases b
  {
  }
}

module Base64Lemmas {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened Base64
  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[|s| - 4..])
    requires !Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 2] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 2..] == Decode1Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidUnpaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 1] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid2PaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 1..] == Decode2Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma EncodeDecodeValid(b: seq<uint8>)
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
    decreases s
  {
  }

  lemma EncodeDecode(b: seq<uint8>)
    ensures Decode(Encode(b)) == Success(b)
    decreases b
  {
  }
}

module Actions {

  import opened Wrappers

  import opened Seq
  datatype ActionInvoke<A, R> = ActionInvoke(input: A, output: R)

  trait {:termination false} Action<A, R> {
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, R>>) returns (r: R)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)
      decreases Modifies

    predicate Invariant()
      reads Modifies
      decreases Modifies

    predicate Ensures(a: A, r: R, attemptsState: seq<ActionInvoke<A, R>>)
      reads Modifies
      decreases Modifies

    ghost const Modifies: set<object>
  }

  trait {:termination false} ActionWithResult<A, R, E> extends Action<A, Result<R, E>> {
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, Result<R, E>>>) returns (r: Result<R, E>)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)
      decreases Modifies
  }

  trait {:termination false} DeterministicAction<A, R> {
    method Invoke(a: A) returns (r: R)
      ensures Ensures(a, r)

    predicate Ensures(a: A, r: R)
  }

  trait {:termination false} DeterministicActionWithResult<A, R, E> extends DeterministicAction<A, Result<R, E>> {
    method Invoke(a: A) returns (r: Result<R, E>)
      ensures Ensures(a, r)
  }

  method DeterministicMap<A, R>(action: DeterministicAction<A, R>, s: seq<A>) returns (res: seq<R>)
    ensures |s| == |res|
    ensures forall i: int :: true && 0 <= i < |s| ==> action.Ensures(s[i], res[i])
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], rs[j])
    {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  method DeterministicMapWithResult<A, R, E>(action: DeterministicActionWithResult<A, R, E>, s: seq<A>) returns (res: Result<seq<R>, E>)
    ensures res.Success? ==> |s| == |res.value|
    ensures res.Success? ==> forall i: int :: true && 0 <= i < |s| ==> action.Ensures(s[i], Success(res.value[i]))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], Success(rs[j]))
    {
      var r :- action.Invoke(s[i]);
      rs := rs + [r];
    }
    return Success(rs);
  }

  method DeterministicFlatMap<A, R>(action: DeterministicAction<A, seq<R>>, s: seq<A>) returns (res: seq<R>)
    ensures forall i: A :: i in s ==> true && exists fm: seq<R> :: action.Ensures(i, fm) && forall k: R | k in fm :: k in res
    decreases action, s
  {
    ghost var parts := [];
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], parts[j]) && forall b: R | b in parts[j] :: b in rs
    {
      var r := action.Invoke(s[i]);
      rs := rs + r;
      parts := parts + [r];
    }
    return rs;
  }

  method DeterministicFlatMapWithResult<A, R, E>(action: DeterministicActionWithResult<A, seq<R>, E>, s: seq<A>)
      returns (res: Result<seq<R>, E>, ghost parts: seq<seq<R>>)
    ensures res.Success? ==> |s| == |parts| && res.value == Flatten(parts) && forall i: int :: 0 <= i < |s| ==> action.Ensures(s[i], Success(parts[i])) && multiset(parts[i]) <= multiset(res.value)
    decreases action, s
  {
    parts := [];
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j: int :: true && 0 <= j < i ==> action.Ensures(s[j], Success(parts[j])) && multiset(parts[j]) <= multiset(rs)
      invariant Flatten(parts) == rs
    {
      var r :- action.Invoke(s[i]);
      rs := rs + r;
      LemmaFlattenConcat(parts, [r]);
      parts := parts + [r];
    }
    return Success(rs), parts;
  }

  method Filter<A>(action: DeterministicAction<A, bool>, s: seq<A>) returns (res: seq<A>)
    ensures |s| >= |res|
    ensures forall j: A :: j in res ==> j in s && action.Ensures(j, true)
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A :: j in rs ==> j in s && action.Ensures(j, true)
    {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }

  method FilterWithResult<A, E>(action: DeterministicActionWithResult<A, bool, E>, s: seq<A>) returns (res: Result<seq<A>, E>)
    ensures res.Success? ==> |s| >= |res.value| && forall j: A :: j in res.value ==> j in s && action.Ensures(j, Success(true))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A :: j in rs ==> j in s && action.Ensures(j, Success(true))
    {
      var r :- action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  method ReduceToSuccess<A, B, E>(action: ActionWithResult<A, B, E>, s: seq<A>)
      returns (res: Result<B, seq<E>>, ghost attemptsState: seq<ActionInvoke<A, Result<B, E>>>)
    requires 0 < |s|
    requires action.Invariant()
    modifies action.Modifies
    ensures 0 < |attemptsState| <= |s|
    ensures forall i: int | 0 <= i < |attemptsState| :: attemptsState[i].input == s[i]
    ensures action.Invariant()
    ensures if res.Success? then Last(attemptsState).output.Success? && Last(attemptsState).output.value == res.value && action.Ensures(Last(attemptsState).input, Last(attemptsState).output, DropLast(attemptsState)) && forall i: int | 0 <= i < |DropLast(attemptsState)| :: attemptsState[i].output.Failure? else |attemptsState| == |s| && forall i: int | 0 <= i < |attemptsState| :: attemptsState[i].output.Failure?
    decreases action.Modifies
  {
    var attemptedResults := [];
    attemptsState := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |attemptsState| == |attemptedResults|
      invariant forall j: int | 0 <= j < |attemptsState| :: attemptsState[j].input == s[j] && attemptsState[j].output.Failure? && attemptedResults[j] == attemptsState[j].output
      invariant action.Invariant()
    {
      var attempt := action.Invoke(s[i], attemptsState);
      attemptsState := attemptsState + [ActionInvoke(s[i], attempt)];
      attemptedResults := attemptedResults + [attempt];
      if attempt.Success? {
        return Success(attempt.value), attemptsState;
      }
    }
    res := Failure(Seq.Map(pluckErrors, attemptedResults));
  }

  function method pluckErrors<B, E>(r: Result<B, E>): (e: E)
    requires r.Failure?
    ensures r.error == e
    decreases r
  {
    r.error
  }
}

module Seq {

  import opened Wrappers

  import Math
  function method First<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[0]
  }

  function method DropFirst<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[1..]
  }

  function method Last<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[|s| - 1]
  }

  function method DropLast<T>(s: seq<T>): seq<T>
    requires |s| > 0
    decreases s
  {
    s[..|s| - 1]
  }

  lemma LemmaLast<T>(s: seq<T>)
    requires |s| > 0
    ensures DropLast(s) + [Last(s)] == s
    decreases s
  {
  }

  lemma LemmaAppendLast<T>(a: seq<T>, b: seq<T>)
    requires 0 < |a + b| && 0 < |b|
    ensures Last(a + b) == Last(b)
    decreases a, b
  {
  }

  lemma LemmaConcatIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == a + b + c
    decreases a, b, c
  {
  }

  predicate IsPrefix<T>(a: seq<T>, b: seq<T>)
    ensures IsPrefix(a, b) ==> |a| <= |b| && a == b[..|a|]
    decreases a, b
  {
    a <= b
  }

  predicate IsSuffix<T>(a: seq<T>, b: seq<T>)
    decreases a, b
  {
    |a| <= |b| &&
    a == b[|b| - |a|..]
  }

  lemma LemmaSplitAt<T>(s: seq<T>, pos: nat)
    requires pos < |s|
    ensures s[..pos] + s[pos..] == s
    decreases s, pos
  {
  }

  lemma LemmaElementFromSlice<T>(s: seq<T>, s': seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |s|
    requires s' == s[a .. b]
    requires a <= pos < b
    ensures pos - a < |s'|
    ensures s'[pos - a] == s[pos]
    decreases s, s', a, b, pos
  {
  }

  lemma LemmaSliceOfSlice<T>(s: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |s|
    requires 0 <= s2 <= e2 <= e1 - s1
    ensures s[s1 .. e1][s2 .. e2] == s[s1 + s2 .. s1 + e2]
    decreases s, s1, e1, s2, e2
  {
  }

  method ToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  function method {:opaque} {:fuel 0, 0} ToSet<T>(s: seq<T>): set<T>
    decreases s
  {
    set x: T {:trigger x in s} | x in s
  }

  lemma LemmaCardinalityOfSet<T>(s: seq<T>)
    ensures |ToSet(s)| <= |s|
    decreases s
  {
  }

  lemma LemmaCardinalityOfEmptySetIs0<T>(s: seq<T>)
    ensures |ToSet(s)| == 0 <==> |s| == 0
    decreases s
  {
  }

  predicate {:opaque} {:fuel 0, 0} HasNoDuplicates<T>(s: seq<T>)
    decreases s
  {
    forall i: int, j: int {:trigger s[i], s[j]} :: 
      0 <= i < |s| &&
      0 <= j < |s| &&
      i != j ==>
        s[i] != s[j]
  }

  lemma {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ LemmaNoDuplicatesInConcat<T>(a: seq<T>, b: seq<T>)
    requires HasNoDuplicates(a)
    requires HasNoDuplicates(b)
    requires multiset(a) !! multiset(b)
    ensures HasNoDuplicates(a + b)
    decreases a, b
  {
  }

  lemma LemmaCardinalityOfSetNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures |ToSet(s)| == |s|
    decreases s
  {
  }

  lemma LemmaNoDuplicatesCardinalityOfSet<T>(s: seq<T>)
    requires |ToSet(s)| == |s|
    ensures HasNoDuplicates(s)
    decreases s
  {
  }

  lemma LemmaMultisetHasNoDuplicates<T>(s: seq<T>)
    requires HasNoDuplicates(s)
    ensures forall x: T {:trigger multiset(s)[x]} | x in multiset(s) :: multiset(s)[x] == 1
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} IndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: 0 <= j < i ==> s[j] != v
    decreases s
  {
    if s[0] == v then
      0
    else
      1 + IndexOf(s[1..], v)
  }

  function method {:opaque} {:fuel 0, 0} IndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: 0 <= j < o.value ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[0] == v then
      Some(0)
    else
      var o': Option<nat> := IndexOfOption(s[1..], v); if o'.Some? then Some(o'.value + 1) else None()
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOf<T(==)>(s: seq<T>, v: T): (i: nat)
    requires v in s
    ensures i < |s| && s[i] == v
    ensures forall j: int {:trigger s[j]} :: i < j < |s| ==> s[j] != v
    decreases s
  {
    if s[|s| - 1] == v then
      |s| - 1
    else
      LastIndexOf(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOfOption<T(==)>(s: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |s| && s[o.value] == v && forall j: int {:trigger s[j]} :: o.value < j < |s| ==> s[j] != v else v !in s
    decreases s
  {
    if |s| == 0 then
      None()
    else if s[|s| - 1] == v then
      Some(|s| - 1)
    else
      LastIndexOfOption(s[..|s| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} Remove<T>(s: seq<T>, pos: nat): (s': seq<T>)
    requires pos < |s|
    ensures |s'| == |s| - 1
    ensures forall i: int {:trigger s'[i], s[i]} | 0 <= i < pos :: s'[i] == s[i]
    ensures forall i: int {:trigger s'[i]} | pos <= i < |s| - 1 :: s'[i] == s[i + 1]
    decreases s, pos
  {
    s[..pos] + s[pos + 1..]
  }

  function method {:opaque} {:fuel 0, 0} RemoveValue<T(==)>(s: seq<T>, v: T): (s': seq<T>)
    ensures v !in s ==> s == s'
    ensures v in s ==> |multiset(s')| == |multiset(s)| - 1
    ensures v in s ==> multiset(s')[v] == multiset(s)[v] - 1
    ensures HasNoDuplicates(s) ==> HasNoDuplicates(s') && ToSet(s') == ToSet(s) - {v}
    decreases s
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in s then
      s
    else
      var i: nat := IndexOf(s, v); assert s == s[..i] + [v] + s[i + 1..]; s[..i] + s[i + 1..]
  }

  function method {:opaque} {:fuel 0, 0} Insert<T>(s: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |s|
    ensures |Insert(s, a, pos)| == |s| + 1
    ensures forall i: int {:trigger Insert(s, a, pos)[i], s[i]} :: 0 <= i < pos ==> Insert(s, a, pos)[i] == s[i]
    ensures forall i: int {:trigger s[i]} :: pos <= i < |s| ==> Insert(s, a, pos)[i + 1] == s[i]
    ensures Insert(s, a, pos)[pos] == a
    ensures multiset(Insert(s, a, pos)) == multiset(s) + multiset{a}
    decreases s, pos
  {
    assert s == s[..pos] + s[pos..];
    s[..pos] + [a] + s[pos..]
  }

  function method {:opaque} {:fuel 0, 0} Reverse<T>(s: seq<T>): (s': seq<T>)
    ensures |s'| == |s|
    ensures forall i: int {:trigger s'[i]} {:trigger s[|s| - i - 1]} :: 0 <= i < |s| ==> s'[i] == s[|s| - i - 1]
    decreases s
  {
    if s == [] then
      []
    else
      [s[|s| - 1]] + Reverse(s[0 .. |s| - 1])
  }

  function method {:opaque} {:fuel 0, 0} Repeat<T>(v: T, length: nat): (s: seq<T>)
    ensures |s| == length
    ensures forall i: nat {:trigger s[i]} | i < |s| :: s[i] == v
    decreases length
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }

  function method {:opaque} {:fuel 0, 0} Unzip<A, B>(s: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(s).0| == |Unzip(s).1| == |s|
    ensures forall i: int {:trigger Unzip(s).0[i]} {:trigger Unzip(s).1[i]} :: 0 <= i < |s| ==> (Unzip(s).0[i], Unzip(s).1[i]) == s[i]
    decreases s
  {
    if |s| == 0 then
      ([], [])
    else
      var (a: seq<A>, b: seq<B>) := Unzip(DropLast(s)); (a + [Last(s).0], b + [Last(s).1])
  }

  function method {:opaque} {:fuel 0, 0} Zip<A, B>(a: seq<A>, b: seq<B>): seq<(A, B)>
    requires |a| == |b|
    ensures |Zip(a, b)| == |a|
    ensures forall i: int {:trigger Zip(a, b)[i]} :: 0 <= i < |Zip(a, b)| ==> Zip(a, b)[i] == (a[i], b[i])
    ensures Unzip(Zip(a, b)).0 == a
    ensures Unzip(Zip(a, b)).1 == b
    decreases a, b
  {
    if |a| == 0 then
      []
    else
      Zip(DropLast(a), DropLast(b)) + [(Last(a), Last(b))]
  }

  lemma /*{:_induction s}*/ LemmaZipOfUnzip<A, B>(s: seq<(A, B)>)
    ensures Zip(Unzip(s).0, Unzip(s).1) == s
    decreases s
  {
  }

  function method {:opaque} {:fuel 0, 0} Max(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Max(s) >= k
    ensures Max(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Max(s[0], Max(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMaxOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Max(a + b) >= Max(a)
    ensures Max(a + b) >= Max(b)
    ensures forall i: int {:trigger i in [Max(a + b)]} :: i in a + b ==> Max(a + b) >= i
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Min(s: seq<int>): int
    requires 0 < |s|
    ensures forall k: int {:trigger k in s} :: k in s ==> Min(s) <= k
    ensures Min(s) in s
    decreases s
  {
    assert s == [s[0]] + s[1..];
    if |s| == 1 then
      s[0]
    else
      Math.Min(s[0], Min(s[1..]))
  }

  lemma /*{:_induction a, b}*/ LemmaMinOfConcat(a: seq<int>, b: seq<int>)
    requires 0 < |a| && 0 < |b|
    ensures Min(a + b) <= Min(a)
    ensures Min(a + b) <= Min(b)
    ensures forall i: int {:trigger i in a + b} :: i in a + b ==> Min(a + b) <= i
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMax(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Max(s[from .. to]) <= Max(s)
    decreases s, from, to
  {
  }

  lemma /*{:_induction s}*/ LemmaSubseqMin(s: seq<int>, from: nat, to: nat)
    requires from < to <= |s|
    ensures Min(s[from .. to]) >= Min(s)
    decreases s, from, to
  {
  }

  function method Flatten<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      s[0] + Flatten(s[1..])
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures Flatten(a + b) == Flatten(a) + Flatten(b)
    decreases a, b
  {
  }

  function method FlattenReverse<T>(s: seq<seq<T>>): seq<T>
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      FlattenReverse(DropLast(s)) + Last(s)
  }

  lemma /*{:_induction a, b}*/ LemmaFlattenReverseConcat<T>(a: seq<seq<T>>, b: seq<seq<T>>)
    ensures FlattenReverse(a + b) == FlattenReverse(a) + FlattenReverse(b)
    decreases a, b
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenAndFlattenReverseAreEquivalent<T>(s: seq<seq<T>>)
    ensures Flatten(s) == FlattenReverse(s)
    decreases s
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthGeSingleElementLength<T>(s: seq<seq<T>>, i: int)
    requires 0 <= i < |s|
    ensures |FlattenReverse(s)| >= |s[i]|
    decreases s, i
  {
  }

  lemma /*{:_induction s}*/ LemmaFlattenLengthLeMul<T>(s: seq<seq<T>>, j: int)
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: |s[i]| <= j
    ensures |FlattenReverse(s)| <= |s| * j
    decreases s, j
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<T, R>(f: T ~> R, s: seq<T>): (result: seq<R>)
    requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures |result| == |s|
    ensures forall i: int {:trigger result[i]} :: 0 <= i < |s| ==> result[i] == f(s[i])
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      []
    else
      [f(s[0])] + Map(f, s[1..])
  }

  function method {:opaque} {:fuel 0, 0} MapWithResult<T, R, E>(f: T ~> Result<R, E>, s: seq<T>): (result: Result<seq<R>, E>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o
    ensures result.Success? ==> |result.value| == |s| && forall i: int :: 0 <= i < |s| ==> f(s[i]).Success? && result.value[i] == f(s[i]).value
    decreases set i: int, o: object? {:trigger o in f.reads(s[i])} | 0 <= i < |s| && o in f.reads(s[i]) :: o, s
  {
    if |s| == 0 then
      Success([])
    else
      var head: R :- f(s[0]); var tail: seq<R> :- MapWithResult(f, s[1..]); Success([head] + tail)
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaMapDistributesOverConcat<T, R>(f: T ~> R, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Map(f, a + b) == Map(f, a) + Map(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<T>(f: T ~> bool, s: seq<T>): (result: seq<T>)
    requires forall i: int :: 0 <= i < |s| ==> f.requires(s[i])
    reads f.reads
    ensures |result| <= |s|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    decreases set _x0: T, _o0: object? | _o0 in f.reads(_x0) :: _o0, s
  {
    if |s| == 0 then
      []
    else
      (if f(s[0]) then [s[0]] else []) + Filter(f, s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFilterDistributesOverConcat<T>(f: T ~> bool, a: seq<T>, b: seq<T>)
    requires forall i: int {:trigger a[i]} :: 0 <= i < |a| ==> f.requires(a[i])
    requires forall j: int {:trigger b[j]} :: 0 <= j < |b| ==> f.requires(b[j])
    ensures Filter(f, a + b) == Filter(f, a) + Filter(f, b)
    decreases a, b
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldLeft<A, T>(f: (A, T) -> A, init: A, s: seq<T>): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      FoldLeft(f, f(init, s[0]), s[1..])
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldLeftDistributesOverConcat<A, T>(f: (A, T) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldLeft(f, init, a + b) == FoldLeft(f, FoldLeft(f, init, a), b)
    decreases a, b
  {
  }

  predicate InvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(b, [x] + xs) &&
      stp(b, x, b') ==>
        inv(b', xs)
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldLeft<A, B>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool, f: (B, A) -> B, b: B, xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b: B, a: A :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldRight<A, T>(f: (T, A) -> A, s: seq<T>, init: A): A
    decreases s
  {
    if |s| == 0 then
      init
    else
      f(s[0], FoldRight(f, s[1..], init))
  }

  lemma {:opaque} /*{:_induction f, a, b}*/ LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, a: seq<T>, b: seq<T>)
    requires 0 <= |a + b|
    ensures FoldRight(f, a + b, init) == FoldRight(f, a, FoldRight(f, b, init))
    decreases a, b
  {
  }

  predicate InvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B :: 
      inv(xs, b) &&
      stp(x, b, b') ==>
        inv([x] + xs, b')
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldRight<A, B>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool, f: (A, B) -> B, b: B, xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a: A, b: B :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
    decreases xs
  {
  }
}

module Math {
  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Max(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      b
    else
      a
  }
}

module Sorting {

  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering, LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow, SelectionSort, StandardLibrary, UInt


  import StandardLibrary

  import opened UInt = StandardLibrary.UInt
  predicate Reflexive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T :: 
      R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T :: 
      R(x, y) &&
      R(y, x) ==>
        x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T :: 
      R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    AntiSymmetric(R) &&
    StandardLibrary.Transitive(R) &&
    Connected(R)
  }

  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>)
    decreases x, y
  {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    n == |x| || (n != |y| && x[n] < y[n]) || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
  }

  lemma /*{:_induction x, n}*/ AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, z, n}*/ AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  method SelectionSort<Data>(a: array<Data>, below: (Data, Data) -> bool)
    requires StandardLibrary.Transitive(below)
    requires Connected(below)
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i: int, j: int :: 0 <= i < j < a.Length ==> below(a[i], a[j])
    decreases a
  {
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall i: int, j: int :: 0 <= i < j < m ==> below(a[i], a[j])
      invariant forall i: int, j: int :: 0 <= i < m <= j < a.Length ==> below(a[i], a[j])
      decreases a.Length - m
    {
      var mindex, n := m, m + 1;
      while n < a.Length
        invariant m <= mindex < n <= a.Length
        invariant forall i: int :: m <= i < n ==> below(a[mindex], a[i])
        decreases a.Length - n
      {
        if !below(a[mindex], a[n]) {
          mindex := n;
        }
        n := n + 1;
      }
      a[m], a[mindex] := a[mindex], a[m];
      m := m + 1;
    }
  }
}

module Streams {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  class SeqReader<T> {
    ghost var Repr: set<object>
    const data: seq<T>
    var pos: nat

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      pos <= |data|
    }

    constructor (s: seq<T>)
      ensures pos == 0
      ensures data[..] == s
      ensures Valid() && fresh(Repr)
      decreases s
    {
      data := s;
      pos := 0;
      Repr := {this};
    }

    method ReadElements(n: nat) returns (elems: seq<T>)
      requires Valid()
      requires n + pos <= |data|
      modifies `pos
      ensures n == 0 ==> elems == []
      ensures n > 0 ==> elems == data[old(pos)..][..n]
      ensures pos == old(pos) + n
      ensures Valid()
      decreases n
    {
      elems := data[pos..][..n];
      pos := pos + n;
      return elems;
    }

    method ReadExact(n: nat) returns (res: Result<seq<T>, string>)
      requires Valid()
      modifies `pos
      ensures n + old(pos) <= |data| <==> res.Success?
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? ==> pos == old(pos) + n
      ensures res.Success? ==> res.value == data[old(pos) .. old(pos) + n]
      ensures res.Failure? ==> n > |data| - pos
      ensures res.Failure? ==> pos == old(pos)
      ensures Valid()
      decreases n
    {
      if n > |data| - pos {
        return Failure(""IO Error: Not enough elements left on stream."");
      } else {
        var elements := ReadElements(n);
        return Success(elements);
      }
    }
  }

  class ByteReader {
    ghost var Repr: set<object>
    const reader: SeqReader<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      reader in Repr &&
      reader.Repr <= Repr &&
      this !in reader.Repr &&
      reader.Valid()
    }

    constructor (s: seq<uint8>)
      ensures reader.data == s
      ensures reader.pos == 0
      ensures Valid() && fresh(Repr)
      decreases s
    {
      var mr := new SeqReader<uint8>(s);
      reader := mr;
      Repr := {this} + mr.Repr;
    }

    method ReadByte() returns (res: Result<uint8, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 1
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 1
      ensures old(reader.pos) + 1 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos)]
      ensures Valid()
    {
      var bytes :- reader.ReadExact(1);
      assert |bytes| == 1;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < n
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? && |res.value| == 0 ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + n
      ensures old(reader.pos) + n <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos) .. old(reader.pos) + n]
      ensures Valid()
      decreases n
    {
      var bytes :- reader.ReadExact(n);
      assert |bytes| == n;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 2
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 2
      ensures old(reader.pos) + 2 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt16(reader.data[old(reader.pos) .. old(reader.pos) + 2])
      ensures Valid()
    {
      var bytes :- reader.ReadExact(2);
      assert |bytes| == 2;
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32, string>)
      requires Valid()
      modifies reader`pos
      ensures Valid()
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 4 && UInt32ToSeq(res.value) == reader.data[old(reader.pos) .. reader.pos]
    {
      var bytes :- reader.ReadExact(4);
      assert |bytes| == 4;
      var n := SeqToUInt32(bytes);
      UInt32SeqDeserializeSerialize(bytes);
      return Success(n);
    }

    method ReadUInt64() returns (res: Result<uint64, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 8
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 8
      ensures old(reader.pos) + 8 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt64(reader.data[old(reader.pos) .. old(reader.pos) + 8])
      ensures Valid()
    {
      var bytes :- reader.ReadExact(8);
      assert |bytes| == 8;
      var n := SeqToUInt64(bytes);
      return Success(n);
    }

    method IsDoneReading() returns (b: bool)
      requires Valid()
      ensures (b && |reader.data| - reader.pos == 0) || (!b && |reader.data| - reader.pos > 0)
      ensures Valid()
    {
      return |reader.data| == reader.pos;
    }

    method GetSizeRead() returns (n: nat)
      requires Valid()
      ensures n == reader.pos
      ensures Valid()
    {
      return reader.pos;
    }
  }

  class SeqWriter<T> {
    ghost var Repr: set<object>
    var data: seq<T>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr
    }

    constructor ()
      ensures data == []
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method WriteElements(elems: seq<T>) returns (n: nat)
      requires Valid()
      modifies `data
      ensures n == |data| - |old(data)| == |elems|
      ensures |elems| == 0 ==> data == old(data)
      ensures |elems| > 0 ==> data == old(data) + elems
      ensures elems == data[|data| - |elems|..]
      ensures Valid()
      decreases elems
    {
      data := data + elems;
      return |elems|;
    }
  }

  class ByteWriter {
    ghost var Repr: set<object>
    const writer: SeqWriter<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      writer in Repr &&
      writer.Repr <= Repr &&
      this !in writer.Repr &&
      writer.Valid()
    }

    constructor ()
      ensures writer.data == []
      ensures Valid() && fresh(Repr)
    {
      var mw := new SeqWriter<uint8>();
      writer := mw;
      Repr := {this} + mw.Repr;
    }

    method WriteByte(n: uint8) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + [n]
      ensures r == 1
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements([n]);
    }

    method WriteBytes(s: seq<uint8>) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + s
      ensures r == |s|
      ensures Valid()
      decreases s
    {
      r := writer.WriteElements(s);
    }

    method WriteUInt16(n: uint16) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt16ToSeq(n)
      ensures r == 2
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt16ToSeq(n));
    }

    method WriteUInt32(n: uint32) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt32ToSeq(n)
      ensures r == 4
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt32ToSeq(n));
    }

    function method GetDataWritten(): (s: seq<uint8>)
      requires Valid()
      reads Repr
      ensures s == writer.data
      ensures Valid()
      decreases Repr
    {
      writer.data
    }

    function method GetSizeWritten(): (n: nat)
      requires Valid()
      reads Repr
      ensures n == |writer.data|
      ensures Valid()
      decreases Repr
    {
      |writer.data|
    }
  }
}

module {:extern ""Sets""} Sets {

  import opened StandardLibrary

  import Seq
  method {:extern ""SetToOrderedSequence""} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    decreases s

  function method {:extern ""SetToOrderedSequence2""} ComputeSetToOrderedSequence2<T(==)>(s: set<seq<T>>, less: (T, T) -> bool): (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    ensures Seq.HasNoDuplicates(res)
    decreases s
}

module Time {

  import opened StandardLibrary

  import opened UInt = StandardLibrary.UInt
  method {:extern ""TimeUtil.Time"", ""CurrentRelativeTime""} GetCurrent() returns (seconds: uint64)
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

module SimpleTypesImpl refines AbstractExampleSimpletypesOperations {
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

  predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
    decreases input, output
  {
    true
  }

  method GetString(config: InternalConfig, input: GetStringInput) returns (output: Result<GetStringOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetStringEnsuresPublicly(input, output)
    decreases ModifiesInternalConfig(config)
  {
    var res := GetStringOutput(result := input.stringValue);
    return Success(res);
  }

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ExampleSimpletypesTypes
}

module {:extern ""Dafny.Example.Simpletypes.Types""} ExampleSimpletypesTypes {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8
  datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)

  datatype EmptyConfig = EmptyConfig

  datatype GetStringInput = GetStringInput(nameonly stringValue: Option<string>)

  datatype GetStringOutput = GetStringOutput(nameonly result: Option<string>)

  class ISimpleTypesServiceClientCallHistory {
    ghost constructor ()
    {
      GetString := [];
    }

    ghost var GetString: seq<DafnyCallEvent<GetStringInput, Result<GetStringOutput, Error>>>
  }

  trait {:termination false} ISimpleTypesServiceClient {
    ghost const Modifies: set<object>

    predicate ValidState()
      ensures ValidState() ==> History in Modifies

    ghost const History: ISimpleTypesServiceClientCallHistory

    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
      decreases input, output

    method GetString(input: GetStringInput) returns (output: Result<GetStringOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetString
      ensures true && ValidState()
      ensures GetStringEnsuresPublicly(input, output)
      ensures History.GetString == old(History.GetString) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
  }

  datatype Error = Collection(list: seq<Error>) | Opaque(obj: object)

  type OpaqueError = e: Error
    | e.Opaque?
    witness *
}

abstract module AbstractExampleSimpletypesService {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ExampleSimpletypesTypes

  import Operations : AbstractExampleSimpletypesOperations
  class SimpleTypesClient extends ISimpleTypesServiceClient {
    constructor (config: Operations.InternalConfig)
      requires Operations.ValidInternalConfig?(config)
      ensures ValidState() && fresh(History) && this.config == config

    const config: Operations.InternalConfig

    predicate ValidState()
      ensures ValidState() ==> Operations.ValidInternalConfig?(config) && History !in Operations.ModifiesInternalConfig(config) && Modifies == Operations.ModifiesInternalConfig(config) + {History}

    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
      decreases input, output
    {
      Operations.GetStringEnsuresPublicly(input, output)
    }

    method GetString(input: GetStringInput) returns (output: Result<GetStringOutput, Error>)
      requires true && ValidState()
      modifies Modifies - {History}, History`GetString
      ensures true && ValidState()
      ensures GetStringEnsuresPublicly(input, output)
      ensures History.GetString == old(History.GetString) + [DafnyCallEvent(input, output)]
      decreases Modifies - {History}
    {
      output := Operations.GetString(config, input);
      History.GetString := History.GetString + [DafnyCallEvent(input, output)];
    }
  }

  function method DefaultEmptyConfig(): EmptyConfig

  method SimpleTypes(config: EmptyConfig := DefaultEmptyConfig()) returns (res: Result<SimpleTypesClient, Error>)
    ensures res.Success? ==> fresh(res.value) && fresh(res.value.Modifies) && fresh(res.value.History) && res.value.ValidState()
    decreases config
}

abstract module AbstractExampleSimpletypesOperations {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened UTF8

  import opened Types = ExampleSimpletypesTypes
  type InternalConfig

  predicate ValidInternalConfig?(config: InternalConfig)

  function ModifiesInternalConfig(config: InternalConfig): set<object>

  predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
    decreases input, output

  method GetString(config: InternalConfig, input: GetStringInput) returns (output: Result<GetStringOutput, Error>)
    requires true && ValidInternalConfig?(config)
    modifies ModifiesInternalConfig(config)
    ensures true && ValidInternalConfig?(config)
    ensures GetStringEnsuresPublicly(input, output)
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
namespace Dafny.Example.Simpletypes.Types {

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
      var oth = other as Dafny.Example.Simpletypes.Types.DafnyCallEvent<I, O>;
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
      string s = "Dafny.Example.Simpletypes.Types_Compile.DafnyCallEvent.DafnyCallEvent";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static Dafny.Example.Simpletypes.Types._IDafnyCallEvent<I, O> Default(I _default_I, O _default_O) {
      return create(_default_I, _default_O);
    }
    public static Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IDafnyCallEvent<I, O>> _TypeDescriptor(Dafny.TypeDescriptor<I> _td_I, Dafny.TypeDescriptor<O> _td_O) {
      return new Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IDafnyCallEvent<I, O>>(Dafny.Example.Simpletypes.Types.DafnyCallEvent<I, O>.Default(_td_I.Default(), _td_O.Default()));
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

  public interface _IEmptyConfig {
    bool is_EmptyConfig { get; }
    _IEmptyConfig DowncastClone();
  }
  public class EmptyConfig : _IEmptyConfig {
    public EmptyConfig() {
    }
    public _IEmptyConfig DowncastClone() {
      if (this is _IEmptyConfig dt) { return dt; }
      return new EmptyConfig();
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Example.Simpletypes.Types.EmptyConfig;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Example.Simpletypes.Types_Compile.EmptyConfig.EmptyConfig";
      return s;
    }
    private static readonly Dafny.Example.Simpletypes.Types._IEmptyConfig theDefault = create();
    public static Dafny.Example.Simpletypes.Types._IEmptyConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IEmptyConfig> _TYPE = new Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IEmptyConfig>(Dafny.Example.Simpletypes.Types.EmptyConfig.Default());
    public static Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IEmptyConfig> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEmptyConfig create() {
      return new EmptyConfig();
    }
    public bool is_EmptyConfig { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IEmptyConfig> AllSingletonConstructors {
      get {
        yield return EmptyConfig.create();
      }
    }
  }

  public interface _IGetStringInput {
    bool is_GetStringInput { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_stringValue { get; }
  }
  public class GetStringInput : _IGetStringInput {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _stringValue;
    public GetStringInput(Wrappers_Compile._IOption<Dafny.ISequence<char>> stringValue) {
      this._stringValue = stringValue;
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> DowncastClone(Wrappers_Compile._IOption<Dafny.ISequence<char>> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Example.Simpletypes.Types.GetStringInput;
      return oth != null && object.Equals(this._stringValue, oth._stringValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._stringValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Example.Simpletypes.Types_Compile.GetStringInput.GetStringInput";
      s += "(";
      s += Dafny.Helpers.ToString(this._stringValue);
      s += ")";
      return s;
    }
    private static readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> theDefault = Wrappers_Compile.Option<Dafny.ISequence<char>>.Default();
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>> _TYPE = new Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>>(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetStringInput create(Wrappers_Compile._IOption<Dafny.ISequence<char>> stringValue) {
      return new GetStringInput(stringValue);
    }
    public bool is_GetStringInput { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_stringValue {
      get {
        return this._stringValue;
      }
    }
  }

  public interface _IGetStringOutput {
    bool is_GetStringOutput { get; }
    Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_result { get; }
  }
  public class GetStringOutput : _IGetStringOutput {
    public readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> _result;
    public GetStringOutput(Wrappers_Compile._IOption<Dafny.ISequence<char>> result) {
      this._result = result;
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> DowncastClone(Wrappers_Compile._IOption<Dafny.ISequence<char>> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Example.Simpletypes.Types.GetStringOutput;
      return oth != null && object.Equals(this._result, oth._result);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._result));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Example.Simpletypes.Types_Compile.GetStringOutput.GetStringOutput";
      s += "(";
      s += Dafny.Helpers.ToString(this._result);
      s += ")";
      return s;
    }
    private static readonly Wrappers_Compile._IOption<Dafny.ISequence<char>> theDefault = Wrappers_Compile.Option<Dafny.ISequence<char>>.Default();
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>> _TYPE = new Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>>(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<Dafny.ISequence<char>>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGetStringOutput create(Wrappers_Compile._IOption<Dafny.ISequence<char>> result) {
      return new GetStringOutput(result);
    }
    public bool is_GetStringOutput { get { return true; } }
    public Wrappers_Compile._IOption<Dafny.ISequence<char>> dtor_result {
      get {
        return this._result;
      }
    }
  }

  public partial class ISimpleTypesServiceClientCallHistory {
    public ISimpleTypesServiceClientCallHistory() {
    }
  }

  public interface ISimpleTypesServiceClient {
    Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> GetString(Wrappers_Compile._IOption<Dafny.ISequence<char>> input);
  }
  public class _Companion_ISimpleTypesServiceClient {
  }

  public interface _IError {
    bool is_Collection { get; }
    bool is_Opaque { get; }
    Dafny.ISequence<Dafny.Example.Simpletypes.Types._IError> dtor_list { get; }
    object dtor_obj { get; }
    _IError DowncastClone();
  }
  public abstract class Error : _IError {
    public Error() { }
    private static readonly Dafny.Example.Simpletypes.Types._IError theDefault = create_Collection(Dafny.Sequence<Dafny.Example.Simpletypes.Types._IError>.Empty);
    public static Dafny.Example.Simpletypes.Types._IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError>(Dafny.Example.Simpletypes.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create_Collection(Dafny.ISequence<Dafny.Example.Simpletypes.Types._IError> list) {
      return new Error_Collection(list);
    }
    public static _IError create_Opaque(object obj) {
      return new Error_Opaque(obj);
    }
    public bool is_Collection { get { return this is Error_Collection; } }
    public bool is_Opaque { get { return this is Error_Opaque; } }
    public Dafny.ISequence<Dafny.Example.Simpletypes.Types._IError> dtor_list {
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
    public readonly Dafny.ISequence<Dafny.Example.Simpletypes.Types._IError> _list;
    public Error_Collection(Dafny.ISequence<Dafny.Example.Simpletypes.Types._IError> list) {
      this._list = list;
    }
    public override _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error_Collection(_list);
    }
    public override bool Equals(object other) {
      var oth = other as Dafny.Example.Simpletypes.Types.Error_Collection;
      return oth != null && object.Equals(this._list, oth._list);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._list));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Example.Simpletypes.Types_Compile.Error.Collection";
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
      var oth = other as Dafny.Example.Simpletypes.Types.Error_Opaque;
      return oth != null && this._obj == oth._obj;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny.Example.Simpletypes.Types_Compile.Error.Opaque";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }

  public partial class OpaqueError {
    private static readonly Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError> _TYPE = new Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError>(Dafny.Example.Simpletypes.Types.Error.Default());
    public static Dafny.TypeDescriptor<Dafny.Example.Simpletypes.Types._IError> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace Dafny.Example.Simpletypes.Types
namespace SimpleTypesImpl_Compile {

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
      var oth = other as SimpleTypesImpl_Compile.Config;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "SimpleTypesImpl_Compile.Config.Config";
      return s;
    }
    private static readonly SimpleTypesImpl_Compile._IConfig theDefault = create();
    public static SimpleTypesImpl_Compile._IConfig Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<SimpleTypesImpl_Compile._IConfig> _TYPE = new Dafny.TypeDescriptor<SimpleTypesImpl_Compile._IConfig>(SimpleTypesImpl_Compile.Config.Default());
    public static Dafny.TypeDescriptor<SimpleTypesImpl_Compile._IConfig> _TypeDescriptor() {
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
    public static Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> GetString(SimpleTypesImpl_Compile._IConfig config, Wrappers_Compile._IOption<Dafny.ISequence<char>> input)
    {
      Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> output = Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError>.Default(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
      Wrappers_Compile._IOption<Dafny.ISequence<char>> _0_res;
      _0_res = (input);
      output = Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError>.create_Success(_0_res);
      return output;
      return output;
    }
  }
} // end of namespace SimpleTypesImpl_Compile
namespace Dafny.Example.Simpletypes {

  public partial class SimpleTypesClient : Dafny.Example.Simpletypes.Types.ISimpleTypesServiceClient {
    public SimpleTypesClient() {
      this._config = SimpleTypesImpl_Compile.Config.Default();
    }
    public void __ctor(SimpleTypesImpl_Compile._IConfig config)
    {
      (this)._config = config;
    }
    public Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> GetString(Wrappers_Compile._IOption<Dafny.ISequence<char>> input)
    {
      Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> output = Wrappers_Compile.Result<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError>.Default(Wrappers_Compile.Option<Dafny.ISequence<char>>.Default());
      Wrappers_Compile._IResult<Wrappers_Compile._IOption<Dafny.ISequence<char>>, Dafny.Example.Simpletypes.Types._IError> _out0;
      _out0 = SimpleTypesImpl_Compile.__default.GetString((this).config, input);
      output = _out0;
      return output;
    }
    public SimpleTypesImpl_Compile._IConfig _config {get; set;}
    public SimpleTypesImpl_Compile._IConfig config { get {
      return this._config;
    } }
  }

  public partial class __default {
    public static Dafny.Example.Simpletypes.Types._IEmptyConfig DefaultEmptyConfig() {
      return Dafny.Example.Simpletypes.Types.EmptyConfig.create();
    }
    public static Wrappers_Compile._IResult<Dafny.Example.Simpletypes.SimpleTypesClient, Dafny.Example.Simpletypes.Types._IError> SimpleTypes(Dafny.Example.Simpletypes.Types._IEmptyConfig config)
    {
      Wrappers_Compile._IResult<Dafny.Example.Simpletypes.SimpleTypesClient, Dafny.Example.Simpletypes.Types._IError> res = default(Wrappers_Compile._IResult<Dafny.Example.Simpletypes.SimpleTypesClient, Dafny.Example.Simpletypes.Types._IError>);
      Dafny.Example.Simpletypes.SimpleTypesClient _1_client;
      Dafny.Example.Simpletypes.SimpleTypesClient _nw0 = new Dafny.Example.Simpletypes.SimpleTypesClient();
      _nw0.__ctor(SimpleTypesImpl_Compile.Config.create());
      _1_client = _nw0;
      res = Wrappers_Compile.Result<Dafny.Example.Simpletypes.SimpleTypesClient, Dafny.Example.Simpletypes.Types._IError>.create_Success(_1_client);
      return res;
      return res;
    }
  }
} // end of namespace Dafny.Example.Simpletypes
namespace _module {

} // end of namespace _module
