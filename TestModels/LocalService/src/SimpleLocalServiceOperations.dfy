// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../Model/SimpleLocalServiceTypes.dfy"

module SimpleLocalServiceOperations refines AbstractSimpleLocalServiceOperations {

  datatype Config = Config

  type InternalConfig = Config
    
  predicate method ValidInternalConfig?(config: InternalConfig)
  {true}

  function ModifiesInternalConfig(config: InternalConfig): set<object>
  {{}}
    
  predicate HelloWorldEnsuresPublicly(input: HelloWorldInput, output: Result<HelloWorldOutput, Error>) {
    true
  }
  
  method HelloWorld ( config: InternalConfig, input: HelloWorldInput )
    returns (output: Result<HelloWorldOutput, Error>) 
  {
    output := Success(HelloWorldOutput(greeting := "Hi there!"));
  }


  predicate SelfReflectionEnsuresPublicly(input: SelfReflectionInput , output: Result<SelfReflectionOutput, Error>) {
    true
  }

  method SelfReflection ( config: InternalConfig , input: SelfReflectionInput )
    returns (output: Result<SelfReflectionOutput, Error>) 
  {
    var innerOutput :- input.client.HelloWorld(HelloWorldInput());
    output := Success(SelfReflectionOutput(
      greeting := "I looked deep within myself, and I said '" + innerOutput.greeting + "'"));
  }
    
}
