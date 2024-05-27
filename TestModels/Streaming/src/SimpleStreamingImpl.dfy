

include "../Model/SimpleStreamingTypes.dfy"

module SimpleStreamingImpl refines AbstractSimpleStreamingOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringKnownValueEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    predicate GetStringUTF8EnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>) {
        true
    }
    method GetString ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringKnownValue ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        expect input.value.Some?;
        expect input.value.value == "TEST_SIMPLE_STRING_KNOWN_VALUE"; // This is done so as to assert that polymorph layer is doing one way conversion right as well.
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
    method GetStringUTF8 ( config: InternalConfig,  input: GetStringInput )
    returns (output: Result<GetStringOutput, Error>) {
        expect input.value.Some?;
        var res := GetStringOutput(value := input.value);
        return Success(res);
    }
}

module Foo {

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