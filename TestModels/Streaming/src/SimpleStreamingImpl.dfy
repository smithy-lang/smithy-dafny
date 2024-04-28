


module Foo {

  // IN STDLIB

  trait Action<T, R> {
    ghost var history: seq<(T, R)>

    ghost predicate Consumes(history: seq<(T, R)>, next: T)
    ghost predicate Produces(history: seq<(T, R)>)
    

    method Call(t: T) returns (r: R)
      requires Consumes(history, t)

  }

  type SingleUseAction<T, R> = a: Action<T, R>
    // TODO: Needs indirection or (!new)
    // | forall history | a.Produces(history) :: |history| <= 1
    | true 
    witness *

  ghost predicate ConsumesAnything<T(!new), R(!new)>(a: Action<T, R>) {
    forall history, next | a.Produces(history) :: a.Consumes(history, next)
  }

  type byte = b: nat | b < 256
  type bytes = seq<byte>

  datatype StreamingBlobRequest = StreamingBlobRequest()
  datatype StreamingBlobResponse = StreamingBlobResponse()

  type Error

  datatype Option<T> = Some(value: T) | None
  datatype Result<T, E> = Success(value: T) | Failure(error: E)

  // GENERATED

  // TODO: Check Smithy spec about when response is received

  // TODO: Spec on when sink will be called vs. onData
  method StreamingBlobInput(input: StreamingBlobRequest, onResult: SingleUseAction<Result<StreamingBlobResponse, Error>, ()>) 
    returns (onInputData: Action<Option<bytes>, ()>)
    // TODO: Should be tightened up to reject any data after None
    ensures ConsumesAnything(onInputData)

  datatype StreamingBlobOutputEvent =
    | StreamingBlobOutputData(data: bytes)
    | StreamingBlobOutputSuccess(response: StreamingBlobResponse)
    | StreamingBlobOutputFailure(error: Error)

  method StreamingBlobOutput(input: StreamingBlobRequest, onResultEvent: Action<StreamingBlobOutputEvent, ()>) 
    // TODO: needs a requires clause about sequences of events the callback will consume

  method StreamingBlobInputAndOutput(input: StreamingBlobRequest, onResultEvent: Action<StreamingBlobOutputEvent, ()>) 
    returns (onInputData: Action<Option<bytes>, ()>)
    // TODO: Should be tightened up to reject any data after None
    ensures ConsumesAnything(onInputData)
    // TODO: needs a requires clause about sequences of events the callback will consume
}

