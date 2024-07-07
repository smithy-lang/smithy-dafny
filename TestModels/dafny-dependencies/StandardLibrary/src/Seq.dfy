module {:options "--function-syntax:4"} Seq {

  /* Returns the last element of a non-empty sequence. */
  function Last<T>(xs: seq<T>): T
    requires |xs| > 0
  {
    xs[|xs|-1]
  }

  function DropLast<T>(xs: seq<T>): seq<T>
    requires |xs| > 0;
  {
    xs[..|xs|-1]
  }

  function {:opaque} Map<T, R>(f: (T ~> R), xs: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
  {
    if |xs| == 0 then []
    else [f(xs[0])] + Map(f, xs[1..])
  }

  function {:opaque} Zip<A,B>(xs: seq<A>, ys: seq<B>): seq<(A, B)>
    requires |xs| == |ys|
    ensures |Zip(xs, ys)| == |xs|
    ensures forall i {:trigger Zip(xs, ys)[i]} :: 0 <= i < |Zip(xs, ys)| ==> Zip(xs, ys)[i] == (xs[i], ys[i])
    ensures Unzip(Zip(xs, ys)).0 == xs
    ensures Unzip(Zip(xs, ys)).1 == ys
  {
    if |xs| == 0 then []
    else Zip(DropLast(xs), DropLast(ys)) + [(Last(xs), Last(ys))]
  }

  function {:opaque} Unzip<A,B>(xs: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(xs).0| == |Unzip(xs).1| == |xs|
    ensures forall i {:trigger Unzip(xs).0[i]} {:trigger Unzip(xs).1[i]}
              :: 0 <= i < |xs| ==> (Unzip(xs).0[i], Unzip(xs).1[i]) == xs[i]
  {
    if |xs| == 0 then ([], [])
    else
      var (a, b):= Unzip(DropLast(xs));
      (a + [Last(xs).0], b + [Last(xs).1])
  }

  /* Returns a constant sequence of a given length. */
  function {:opaque} Repeat<T>(v: T, length: nat): (xs: seq<T>)
    ensures |xs| == length
    ensures forall i: nat | i < |xs| :: xs[i] == v
  {
    seq(length, i => v)
  }

  function {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, xs: seq<T>): A
  {
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  lemma FoldLeftNewRightElement<A,T>(f: (A, T) -> A, init: A, xs: seq<T>, x: T)
    ensures FoldLeft(f, init, xs + [x]) == f(FoldLeft(f, init, xs), x)
  {
    reveal FoldLeft();
    if |xs| == 0 {
    } else {
      FoldLeftNewRightElement(f, init, xs[1..], x);
      assert FoldLeft(f, init, xs[1..] + [x]) == f(FoldLeft(f, init, xs[1..]), x);
      assert xs == [xs[0]] + xs[1..];
      assert FoldLeft(f, init, xs[1..] + [x]) == f(FoldLeft(f, init, xs[1..]), x);
      reveal FoldLeft();
      assert FoldLeft(f, init, xs) == FoldLeft(f, f(init, xs[0]), xs[1..]);
      assert FoldLeft(f, init, xs + [x]) == f(FoldLeft(f, init, xs), x);
    }
  }
}