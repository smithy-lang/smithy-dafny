/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:options "--function-syntax:4"} StandardLibrary.Streams {

  import opened Std.Wrappers
  import opened Std.Actions
  import opened Std.BulkActions
  import opened Std.Producers
  import opened Std.Collections.Seq
  import opened Std.Termination

  trait DataStream<T, E> {

    function ContentLength(): Option<nat>

    predicate Replayable()

    method Reader() returns (p: Producer<Batched<T, E>>)
      ensures 
        && p.Valid()
        && fresh(p.Repr)
        && p.history == []
        && (ContentLength().Some? ==> p.Remaining() == Some(ContentLength().value as int + 1))
  }

  class SeqDataStream<T, E> extends DataStream<T, E> {

    const s: seq<T>

    constructor (s: seq<T>)
      ensures this.s == s
    {
      this.s := s;
    }

    function ContentLength(): Option<nat> {
      Some(|s|)
    }

    predicate Replayable() {
      true
    }

    method Reader() returns (p: Producer<Batched<T, E>>)
      ensures 
        && p.Valid()
        && fresh(p.Repr)
        && p.history == []
        && (ContentLength().Some? ==> p.Remaining() == Some(ContentLength().value + 1))
    {
      var data := new BatchReader(s);
      var eoi := new SeqReader([EndOfInput]);
      p := new ConcatenatedProducer(data, eoi);
    }
  }

}