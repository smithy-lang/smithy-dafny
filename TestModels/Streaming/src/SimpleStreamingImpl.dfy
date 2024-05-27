


module StdLib {

  // TODO: Add to actual Actions library:
  // useful pattern to add an Action<Command, Result> facade
  // to a set of methods that participate in a protocol.
  // Then you have a history that ties the behavior
  // of the methods together,
  // supporting constraints on the order of calls etc.
  trait Action<T, R> {
    ghost var history: seq<(T, R)>

    predicate Consumes(history: seq<(T, R)>, next: T)
    predicate Produces(history: seq<(T, R)>)
    

    method Call(t: T) returns (r: R)
      // requires Consumes(history, t)

  }

  // TODO: could use different words for calling when there is no input/no output
  method Call<T>(a: Action<T, ()>, t: T) {
    var _ := a.Call(t);
  }

  type SingleUseAction<T, R> = a: Action<T, R>
    // TODO: Needs indirection or (!new)
    // TODO: Not quite right, SingleUseAction should be a way of saying
    // "I will only call this once"
    // | forall history | a.Produces(history) :: |history| <= 1
    | true 
    witness *

  predicate ConsumesAnything<T(!new), R(!new)>(a: Action<T, R>) {
    forall history, next | a.Produces(history) :: a.Consumes(history, next)
  }

  // TODO: consumes any None-terminated sequence of inputs
  predicate ConsumesTerminated<T(!new), R(!new)>(a: Action<Option<T>, R>)

  type byte = b: nat | b < 256
  type bytes = seq<byte>

  datatype Option<T> = Some(value: T) | None
  datatype Result<T, E> = Success(value: T) | Failure(error: E)
}

module Foo {

  import opened StdLib  

  datatype StreamingBlobRequest = StreamingBlobRequest()
  datatype StreamingBlobResponse = StreamingBlobResponse()

  type Error

  // GENERATED

  // TODO: Check Smithy spec about when response is received
  // TODO: Actions pretty much always have to return Results/Outcomes

  method StreamingBlobInput(input: StreamingBlobRequest, onResult: SingleUseAction<Result<StreamingBlobResponse, Error>, ()>) 
    returns (onInputData: Action<Option<bytes>, ()>)
    ensures ConsumesTerminated(onInputData)

  datatype StreamingBlobOutputEvent =
    | StreamingBlobOutputData(data: bytes)
    | StreamingBlobOutputSuccess(response: StreamingBlobResponse)
    | StreamingBlobOutputFailure(error: Error)

  method StreamingBlobOutput(input: StreamingBlobRequest, onResultEvent: Action<StreamingBlobOutputEvent, ()>) 
    // TODO: needs a requires clause about sequences of events the callback will consume

  method StreamingBlobInputAndOutput(input: StreamingBlobRequest, onResultEvent: Action<StreamingBlobOutputEvent, ()>) 
    returns (onInputData: Action<Option<bytes>, ()>)
    ensures ConsumesTerminated(onInputData)
    // TODO: needs a requires clause about sequences of events the callback will consume
}

// Synchronous-only style
// TODO: Show how to wrap this interface around asynchronous AWS service calls?
module DafnyStyle {

  import opened StdLib  

  datatype StreamingBlobRequest = StreamingBlobRequest()
  datatype StreamingBlobResponse = StreamingBlobResponse()

  type Error

  // TODO: Spec on when sink will be called vs. onData
  method StreamingBlobInput(input: StreamingBlobRequest) 
    returns (onInputData: Action<Option<bytes>, 
                                 Option<Result<StreamingBlobResponse, Error>>>)
    ensures ConsumesTerminated(onInputData)
    // TODO: With @requiresLength, ensures something about |flattened(produced(onInputData))|

  datatype StreamingBlobOutputEvent =
    | StreamingBlobOutputData(data: bytes)
    | StreamingBlobOutputSuccess(response: StreamingBlobResponse)
    | StreamingBlobOutputFailure(error: Error)

  method StreamingBlobOutput(input: StreamingBlobRequest) 
    returns (resultIter: Action<(), StreamingBlobOutputEvent>)
    ensures ConsumesAnything(resultIter)
    // TODO: ensures Enumerator(resultIter), or a variant of it that can error

  method StreamingBlobInputAndOutput(input: StreamingBlobRequest) 
    // Two different ways to implement this around e.g. S3:
    // * Send input, block on next output event
    // * Send input, return 
    returns (onInputData: Action<Option<bytes>, StreamingBlobOutputEvent>)
    ensures ConsumesTerminated(onInputData)
}

module Bar {
  import opened StdLib
  import opened Foo

  method Consumer() {

    var input := StreamingBlobRequest();

    var result: StreamingBlobResponse;
    // TODO: store in result
    var onResult: SingleUseAction<Result<StreamingBlobResponse, Error>, ()>;
    
    var onInputData := StreamingBlobInput(input, onResult);
    Call(onInputData, Some([1, 2]));
    Call(onInputData, Some([3, 4, 5]));
    Call(onInputData, None);

    // result now has the result
    // TODO: how to express that specification?
    // TODO: Could have

  }
}