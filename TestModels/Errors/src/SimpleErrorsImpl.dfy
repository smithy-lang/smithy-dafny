include "../Model/SimpleErrorsTypes.dfy"

module SimpleErrorsImpl refines AbstractSimpleErrorsOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate AlwaysErrorEnsuresPublicly(input: GetErrorsInput, output: Result<GetErrorsOutput, Error>) {
    true
  }
  predicate AlwaysMultipleErrorsEnsuresPublicly(input: GetErrorsInput, output: Result<GetErrorsOutput, Error>) {
    true
  }
  predicate AlwaysNativeErrorEnsuresPublicly(input: GetErrorsInput, output: Result<GetErrorsOutput, Error>) {
    true
  }
  method AlwaysError ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {  
    // TODO: input.value will not necessarily be non-empty when we remove the `@required` field from message.
    // However, it is non-empty for now. So `expect .. Some?` is a valid statement.
    // We should remove this check as part of SIM CrypTool-5085
    expect input.value.Some?;

    var res := SimpleErrorsException(message := input.value.value);

    return Failure(res);
  }

  method AlwaysMultipleErrors ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {
    // TODO: input.value will not necessarily be non-empty when we remove the `@required` field from message.
    // However, it is non-empty for now. So `expect .. Some?` is a valid statement.
    // We should remove this check as part of SIM CrypTool-5085
    expect input.value.Some?;

    // TODO: Make this a Collection.
    // As-is, generated Dotnet code does not understand how to convert a Collection error.
    // (This is in the ToDafny_CommonError and FromDafny_CommonError functions.)
    // Generated code will throw a default OpaqueError when it sees a Collection.
    // We would need to extend the codegen to handle Collections.
    var res := SimpleErrorsException(message := input.value.value);

    return Failure(res);
  }

  method AlwaysNativeError ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {
    // TODO: input.value will not necessarily be non-empty when we remove the `@required` field from message.
    // However, it is non-empty for now. So `expect .. Some?` is a valid statement.
    // We should remove this check as part of SIM CrypTool-5085
    expect input.value.Some?;

    // TODO: Make this use Opaque error as part of SIM CrypTool-5085
    var res := SimpleErrorsException(message := input.value.value);

    return Failure(res);
  }
}