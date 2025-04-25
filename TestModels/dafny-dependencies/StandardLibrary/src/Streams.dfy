/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:options "--function-syntax:4"} StandardLibrary.Streams {

  import opened Std.Wrappers
  import opened Std.Actions
  import opened Std.BulkActions
  import opened Std.Producers
  import opened Std.BoundedInts
  import opened Std.Collections.Seq
  import opened Std.Termination

  //
  // A data stream, i.e. a fallable producer of batches of values.
  //
  trait DataStream<E> {

    function ContentLength(): Option<nat>

    method Reader() returns (p: Producer<StreamedValue<uint8, E>>)
      ensures 
        && p.Valid()
        && fresh(p.Repr)
        && p.history == []
        && (ContentLength().Some? ==> p.Remaining() == Some(ContentLength().value as int + 1))
  }

  class SeqDataStream<E> extends DataStream<E> {

    const s: seq<uint8>

    constructor (s: seq<uint8>)
      ensures this.s == s
    {
      this.s := s;
    }

    function ContentLength(): Option<nat> {
      Some(|s|)
    }

    method Reader() returns (p: Producer<StreamedValue<uint8, E>>)
      ensures 
        && p.Valid()
        && fresh(p.Repr)
        && p.history == []
        && (ContentLength().Some? ==> p.Remaining() == Some(ContentLength().value + 1))
    {
      var data := new BatchReader(s);
      var eoi := new SeqReader([None]);
      p := new ConcatenatedProducer(data, eoi);
    }
  }

}