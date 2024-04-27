


module Foo {
  trait Action<T, R> {
    method Call(t: T) returns (r: R)
  }

  type byte = b: nat | b < 256
  type bytes = seq<byte>

  datatype StreamingBlobInputRequest = StreamingBlobInputRequest()
  datatype StreamingBlobInputResponse = StreamingBlobInputResponse()

  // TODO: Check Smithy spec about when response is received

  method StreamingBlobInput(input: StreamingBlobInputRequest, sink: Action<StreamingBlobInputResponse, ()>) 
    returns (onData: Action<bytes, ()>)


  method StreamingBlobOutput(input: StreamingBlobInputRequest, sink: Action<bytes, ()>) 
    returns (response: StreamingBlobInputResponse)


  method StreamingBlobInputAndOutput(input: StreamingBlobInputRequest, sink: Action<bytes, ()>) 
    returns (response: StreamingBlobInputResponse, onData: Action<bytes, ()>)
}

