// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/AwsCryptographyMaterialProvidersTypesWrapped.dfy"

module {:options "-functionSyntax:4"} JSONHelpers {
  import JSON.API
  import BoundedInts
  import opened JSON.Values
  import opened Wrappers
  import UTF8
  import Types = AwsCryptographyMaterialProvidersTypes

  function BvToBytes(bits: seq<bv8>): seq<BoundedInts.uint8>
  {
    seq(|bits|, i requires 0 <= i < |bits| => bits[i] as BoundedInts.byte)
  }

  function BytesBv(bits: seq<BoundedInts.uint8>): seq<bv8>
  {
    seq(|bits|, i requires 0 <= i < |bits| => bits[i] as bv8)
  }

  function Get(key: string, obj: seq<(string, JSON)>)
    : (output: Result<Values.JSON, string>)
  {
    if |obj| == 0 then
      Failure("Key: " + key + " does not exist")
    else if obj[0].0 == key then
      Success(obj[0].1)
    else
      Get(key, obj[1..])
  }

  function GetString(key: string, obj: seq<(string, JSON)>)
    : Result<string, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.String?, "Not a string");
    Success(obj.str)
  }

  function GetBool(key: string, obj: seq<(string, JSON)>)
    : Result<bool, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Bool?, "Not a bool");
    Success(obj.b)
  }

  function GetNat(key: string, obj: seq<(string, JSON)>)
    : Result<nat, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Number?, "Not a number");
    :- Need(0 < obj.num.n, "Not a nat");
    // This may not be adequate
    Success(obj.num.n)
  }

  function GetPositiveLong(key: string, obj: seq<(string, JSON)>)
    : Result<BoundedInts.int64, string>
  {
    var n :- GetNat(key, obj);
    :- Need(n <= BoundedInts.INT64_MAX as nat, "Int64 Overflow");
    Success(n as BoundedInts.int64)
  }

  function GetPositiveInteger(key: string, obj: seq<(string, JSON)>)
    : Result<BoundedInts.int32, string>
  {
    var n :- GetNat(key, obj);
    :- Need(n <= BoundedInts.INT32_MAX as nat, "Int32 Overflow");
    Success(n as BoundedInts.int32)
  }


  function GetOptionalString(key: string, obj: seq<(string, JSON)>)
    : Result<Option<string>, string>
  {
    var obj := Get(key, obj).ToOption();
    if obj.Some? then
      :- Need(obj.value.String?, "Not a string");
      Success(Some(obj.value.str))
    else
      Success(None)
  }

  function GetOptionalPositiveLong(key: string, obj: seq<(string, JSON)>)
    : Result<Option<BoundedInts.int64>, string>
  {
    var obj := Get(key, obj).ToOption();
    if obj.Some? then
      :- Need(obj.value.Number?, "Not a number");
      :- Need(0 <= obj.value.num.n <= BoundedInts.INT64_MAX as nat, "Int64 Overflow");
      Success(Some(obj.value.num.n as BoundedInts.int64))
    else
      Success(None)
  }

  function GetObject(key: string, obj: seq<(string, JSON)>)
    : Result<seq<(string, JSON)>, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Object?, "Not an object");
    Success(obj.obj)
  }

  function GetArray(key: string, obj: seq<(string, JSON)>)
    : Result<seq<JSON>, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Array?, "Not an array");
    Success(obj.arr)
  }

  function GetArrayString(key: string, obj: seq<(string, JSON)>)
    : Result<seq<string>, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Array? && forall s <- obj.arr :: s.String?, "Not an array of strings");
    var arr := obj.arr;
    Success(seq(|arr|, n requires 0 <= n < |arr| => arr[n].str))
  }

  function GetArrayObject(key: string, obj: seq<(string, JSON)>)
    : Result<seq<seq<(string, JSON)>>, string>
  {
    var obj :- Get(key, obj);
    :- Need(obj.Array? && forall s <- obj.arr :: s.Object?, "Not an array of objects");
    var arr := obj.arr;
    Success(seq(|arr|, n requires 0 <= n < |arr| => arr[n].obj))
  }

  function SmallObjectToStringStringMap(key: string, obj: seq<(string, JSON)>)
    : Result<map<string, string>, string>
  {
    var item :- Get(key, obj);
    JsonObjectToStringStringMap(item)
  }

  function GetOptionalSmallObjectToStringStringMap(key: string, obj: seq<(string, JSON)>)
    : Result<Option<map<string, string>>, string>
  {
    var item := Get(key, obj).ToOption();
    if item.Some? then
      var m :- JsonObjectToStringStringMap(item.value);
      Success(Some(m))
    else
      Success(None)
  }

  function printJson(j: JSON) : (){()} by method {print j, "\n", "\n"; return ();}

  function JsonObjectToStringStringMap(item: JSON)
    : Result<map<string, string>, string>
  {
    :- Need(item.Object?, "Not an object");
    var obj := item.obj;
    :- Need(forall t <- obj :: t.1.String?, "Not a string string object");
    // This is an expensive check for large objects.
    :- Need(forall i,j | 0 <= i < j < |obj| :: obj[i].0 != obj[j].0,
            "JSON serialization Error");
    Success(map t <- obj :: t.0 := t.1.str)
  }


  function utf8EncodePair(key: string, value: string):
    (res: Result<(UTF8.ValidUTF8Bytes, UTF8.ValidUTF8Bytes), string>)
  {
    var utf8Key :- UTF8.Encode(key);
    var utf8Value :- UTF8.Encode(value);

    Success((utf8Key, utf8Value))
  }

  // TODO: These EncryptionContext methods can be removed once we move to UTF8 strings
  function utf8EncodeMap(mapStringString: map<string, string>):
    (res: Result<Types.EncryptionContext, string>)
  {
    if |mapStringString| == 0 then
      Success(map[])
    else

      var encodedResults := map key <- mapStringString :: key := utf8EncodePair(key, mapStringString[key]);
      :- Need(forall r <- encodedResults.Values :: r.Success?, "String can not be UTF8 Encoded?");

      Success(map r <- encodedResults.Values :: r.value.0 := r.value.1)
  }

  function utf8EncodeSeq(seqOfStrings: seq<string>)
    :(res: Result<seq<Types.Utf8Bytes>, string>)
  {
    var encodedResults := seq(|seqOfStrings|, i requires 0 <= i < |seqOfStrings| => UTF8.Encode(seqOfStrings[i]));
    :- Need(forall r <- encodedResults :: r.Success?, "String can not be UTF8 Encoded?");
    Success(seq(|encodedResults|, i requires 0 <= i < |encodedResults| => encodedResults[i].value))
  }

  lemma GotInParent(key: string, obj: seq<(string, JSON)>)
    ensures Get(key, obj).Success? ==> (key, Get(key, obj).value) in obj
  {}

  lemma GetWillDecreaseSize(key: string, got: JSON, j: JSON)
    requires
      && j.Object?
      && Get(key, j.obj).Success?
      && Get(key, j.obj).value == got
    ensures Size(got) < Size(j)
  {
    GotInParent(key, j.obj);
    var i :| 0 <= i < |j.obj| && (key, got) == j.obj[i];

    calc {
      Size(j);
    ==
      Size(Object(j.obj));
    == {assert j.obj == j.obj[..i] + j.obj[i..];}
      Size(Object(j.obj[..i] + j.obj[i..]));
    ==
      SizeObject(j.obj[..i] + j.obj[i..]);
    == {SizeObjectIsAssociative(j.obj[..i], j.obj[i..]);}
      SizeObject(j.obj[..i]) + SizeObject(j.obj[i..]) - 1;
    ==
      SizeObject(j.obj[..i]) + Size(got) + SizeObject(j.obj[i..][1..]) - 1;
    ==
      Size(got) + SizeObject(j.obj[..i]) + SizeObject(j.obj[i..][1..]) - 1;
    == {SizeObjectIsAssociative(j.obj[..i], j.obj[i..][1..]);}
      Size(got) + SizeObject(j.obj[..i] + j.obj[i..][1..]);
    >
      Size(got);
    }
  }

  lemma SizeObjectIsAssociative(o1: seq<(string, JSON)>, o2: seq<(string, JSON)>)
    ensures SizeObject(o1) + SizeObject(o2) - 1 == SizeObject(o1 + o2)
  {
    if |o1| == 0 {
      calc {
        SizeObject(o1) + SizeObject(o2) - 1;
      == {assert SizeObject(o1) == 1;}
        SizeObject(o2);
      == {assert o1 + o2 == o2;}
        SizeObject(o1 + o2);
      }
    } else {
      calc {
        SizeObject(o1 + o2);
      == // () help Dafny combine and split things
        SizeObject((o1 + o2));
      ==
        Size((o1 + o2)[0].1) + SizeObject((o1 + o2)[1..]);
      == {assert o1[0] == (o1 + o2)[0];}
        Size(o1[0].1) + SizeObject((o1 + o2)[1..]);
      == {assert (o1 + o2)[1..] == o1[1..] + o2;}
        Size(o1[0].1) + SizeObject(o1[1..] + o2);
      }
    }
  }


  lemma ElementOfArrayWillDecreaseSize(element: JSON, got: JSON)
    requires got.Array?
    requires element in got.arr
    ensures Size(element) < Size(got)
  {
    if got.arr == [] {
    } else {
      var i :| 0 <= i < |got.arr| && element == got.arr[i];

      calc {
        Size(got);
      ==
        Size(Array(got.arr));
      == {assert got.arr == got.arr[..i] + got.arr[i..];}
        Size(Array(got.arr[..i] + got.arr[i..]));
      ==
        SizeArray(got.arr[..i] + got.arr[i..]);
      == {SizeArrayIsAssociative(got.arr[..i], got.arr[i..]);}
        SizeArray(got.arr[..i]) + SizeArray(got.arr[i..]) - 1;
      ==
        SizeArray(got.arr[..i]) + Size(element) + SizeArray(got.arr[i..][1..]) - 1;
      ==
        Size(element) + SizeArray(got.arr[..i]) + SizeArray(got.arr[i..][1..]) - 1;
      == {SizeArrayIsAssociative(got.arr[..i], got.arr[i..][1..]);}
        Size(element) + SizeArray(got.arr[..i] + got.arr[i..][1..]);
      >
        Size(element);
      }
    }
  }

  lemma ElementsOfArrayWillDecreaseSize(got: JSON)
    requires got.Array?
    ensures forall element <- got.arr :: Size(element) < Size(got)
  {
    forall element <- got.arr
      ensures Size(element) < Size(got)
    {
      ElementOfArrayWillDecreaseSize(element, got);
    }
  }

  lemma SizeArrayIsAssociative(o1: seq<JSON>, o2: seq<JSON>)
    ensures SizeArray(o1) + SizeArray(o2) - 1 == SizeArray(o1 + o2)
  {
    if |o1| == 0 {
      calc {
        SizeArray(o1) + SizeArray(o2) - 1;
      == {assert SizeArray(o1) == 1;}
        SizeArray(o2);
      == {assert o1 + o2 == o2;}
        SizeArray(o1 + o2);
      }
    } else {
      calc {
        SizeArray(o1 + o2);
      == // () help Dafny combine and split things
        SizeArray((o1 + o2));
      ==
        Size((o1 + o2)[0]) + SizeArray((o1 + o2)[1..]);
      == {assert o1[0] == (o1 + o2)[0];}
        Size(o1[0]) + SizeArray((o1 + o2)[1..]);
      == {assert (o1 + o2)[1..] == o1[1..] + o2;}
        Size(o1[0]) + SizeArray(o1[1..] + o2);
      }
    }
  }

  ghost function Size(j: JSON): nat
    ensures 0 < Size(j)
  {
    match j
    case Array(a) => SizeArray(a)
    case Object(o) => SizeObject(o)
    case _ => 1
  }

  ghost function SizeArray(a: seq<JSON>): nat
  {
    if |a| == 0 then
      1
    else
      Size(a[0]) + SizeArray(a[1..])
  }

  ghost function SizeObject(o: seq<(string,JSON)>): nat
  {
    if |o| == 0 then
      1
    else
      Size(o[0].1) + SizeObject(o[1..])
  }
}
