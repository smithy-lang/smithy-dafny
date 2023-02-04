include "../Model/SimpleErrorsTypes.dfy"

module SimpleErrorsImpl refines AbstractSimpleErrorsOperations  {
  datatype Config = Config
  type InternalConfig = Config
  predicate ValidInternalConfig?(config: InternalConfig)
  {true}
  function ModifiesInternalConfig(config: InternalConfig) : set<object>
  {{}}
  predicate AlwaysErrorEnsuresPublicly(input: AlwaysErrorInput, output: Result<AlwaysErrorOutput, Error>) {
    true
  }
  predicate AlwaysMultipleErrorsEnsuresPublicly(input: GetErrorsInput, output: Result<GetErrorsOutput, Error>) {
    true
  }
  predicate AlwaysNativeErrorEnsuresPublicly(input: GetErrorsInput, output: Result<GetErrorsOutput, Error>) {
    true
  }
  method AlwaysError ( config: InternalConfig,  input: AlwaysErrorInput )
    returns (output: Result<AlwaysErrorOutput, Error>)
  {
    expect input.value.Some?;

    var res := AlwaysErrorOutput(value := input.value);
    expect res.value.Some?;

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
  }

  method AlwaysMultipleErrors ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {
    expect input.value.Some?;

    var res := GetErrorsOutput(value := input.value);
    expect res.value.Some?;

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
  }

  method AlwaysNativeError ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {
    expect input.value.Some?;

    var res := GetErrorsOutput(value := input.value);
    expect res.value.Some?;

    // Validate values: input is the same as the output
    expect res.value.value == input.value.value;

    return Success(res);
  }
}