// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
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

    var res := Error.CollectionOfErrors(
      list := [ SimpleErrorsException(message := input.value.value) ],
      message := "Something");

    return Failure(res);
  }

  method AlwaysNativeError ( config: InternalConfig,  input: GetErrorsInput )
    returns (output: Result<GetErrorsOutput, Error>)
  {
      // The SomeOpaqueGeneratedTypeForTesting class is standing in as an extern.
      // Ideally, this would be modelled as an extern, but this is "good enough".
      // TODO: Rewrite this as an actual extern.
      var opaqueObject := new SomeOpaqueGeneratedTypeForTesting();

      var res := Error.Opaque( obj := opaqueObject, alt_text := "Some Generated Test" );

      return Failure(res);
  }

  class SomeOpaqueGeneratedTypeForTesting {
    constructor(){}
  }
}
