include "../Model/SimpleStreamingTypes.dfy"

module Chunker {

  import Std.BoundedInts

  import opened Std.Wrappers
  import opened Types = SimpleStreamingTypes
  import opened StandardLibrary.UInt
  import opened Std.Enumerators
  import opened Std.Aggregators

  // An example of a Pipeline, which processes chunks of bytes
  // as they flow through a stream.
  // Pipelines let you define a stream transformation once
  // in a way that allows external code to apply it to either
  // push or pull-based streams:
  // when a chunk becomes available to the pipeline,
  // zero or more chunks are made available downstream.
  @AssumeCrossModuleTermination
  class Chunker extends Pipeline<BoundedInts.bytes, BoundedInts.bytes> {

    const chunkSize: CountingInteger
    var chunkBuffer: BoundedInts.bytes

    constructor(upstream: Enumerator<BoundedInts.bytes>, chunkSize: CountingInteger)
      ensures Valid()
      ensures history == []
    {
      this.buffer := new Collector<BoundedInts.bytes>();
      this.upstream := upstream;

      this.chunkSize := chunkSize;
      chunkBuffer := [];
      history := [];
      Repr := {this} + upstream.Repr;
      new;
      assume {:axiom} Valid();
    }

    method Process(event: Option<BoundedInts.bytes>, a: Accumulator<BoundedInts.bytes>)
      requires Valid()
      requires a.Valid()
      requires Repr !! a.Repr
      modifies Repr, a.Repr
      ensures a.ValidAndDisjoint()
    {
      assert this in Repr;
      assert this !in a.Repr;
      match event {
        case Some(bits) => {
          chunkBuffer := chunkBuffer + bits;
        }
        case None => return;
      }

      while chunkSize as int <= |chunkBuffer| 
        invariant a.ValidAndDisjoint()
      {
        a.CanConsumeAll(a.history, chunkBuffer[..chunkSize]);
        a.Accept(chunkBuffer[..chunkSize]);
        chunkBuffer := chunkBuffer[chunkSize..];
      }
      
      if event == None {
        if 0 < |chunkBuffer| {
          var _ := a.Invoke(chunkBuffer);
        }
      }
    }
  }
}