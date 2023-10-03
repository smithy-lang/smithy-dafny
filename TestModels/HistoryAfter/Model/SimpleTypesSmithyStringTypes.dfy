// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../dafny-dependencies/StandardLibrary/src/Index.dfy"
 module {:extern "simple.types.smithystring.internaldafny.types" } SimpleTypesSmithyStringTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Histories

 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 datatype GetStringInput = | GetStringInput (
 nameonly value: Option<string>
 )
 datatype GetStringOutput = | GetStringOutput (
 nameonly value: Option<string>
 )
 datatype SimpleStringConfig = | SimpleStringConfig (
 
 )

class GetStringEvent extends Event {
  const input: GetStringInput
  const output: Result<GetStringOutput, Error>
  ghost constructor(input: GetStringInput, output: Result<GetStringOutput, Error>) 
    ensures this.input == input
    ensures this.output == output
  {
    this.input := input;
    this.output := output;
  }
  static function NthLast(history: History, n: nat): GetStringEvent
    requires 
      && n < |history.events|
      && var e: Event := history.events[|history.events| - 1 - n];
      && e is GetStringEvent
    reads history
  {
    var e: Event := history.events[|history.events| - 1 - n];
    e as GetStringEvent
  }

}
class GetStringSingleValueEvent extends Event {
  const input: GetStringInput
  const output: Result<GetStringOutput, Error>
  ghost constructor(input: GetStringInput, output: Result<GetStringOutput, Error>) 
    ensures this.input == input
    ensures this.output == output
  {
    this.input := input;
    this.output := output;
  }
  static function NthLast(history: History, n: nat): GetStringSingleValueEvent
    requires 
      && n < |history.events|
      && var e: Event := history.events[|history.events| - 1 - n];
      && e is GetStringSingleValueEvent
    reads history
  {
    var e: Event := history.events[|history.events| - 1 - n];
    e as GetStringSingleValueEvent
  }
}
class GetStringUTF8Event extends Event {
  const input: GetStringInput
  const output: Result<GetStringOutput, Error>
  ghost constructor(input: GetStringInput, output: Result<GetStringOutput, Error>) 
    ensures this.input == input
    ensures this.output == output
  {
    this.input := input;
    this.output := output;
  }
  static function NthLast(history: History, n: nat): GetStringUTF8Event
    requires 
      && n < |history.events|
      && var e: Event := history.events[|history.events| - 1 - n];
      && e is GetStringUTF8Event
    reads history
  {
    var e: Event := history.events[|history.events| - 1 - n];
    e as GetStringUTF8Event
  }
}



 trait {:termination false} ISimpleTypesStringClient
 {
 // Helper to define any additional modifies/reads clauses.
 // If your operations need to mutate state,
 // add it in your constructor function:
 // Modifies := {your, fields, here, History};
 // If you do not need to mutate anything:
// Modifies := {History};

 ghost const Modifies: set<object>
 // For an unassigned field defined in a trait,
 // Dafny can only assign a value in the constructor.
 // This means that for Dafny to reason about this value,
 // it needs some way to know (an invariant),
 // about the state of the object.
 // This builds on the Valid/Repr paradigm
 // To make this kind requires safe to add
 // to methods called from unverified code,
 // the predicate MUST NOT take any arguments.
 // This means that the correctness of this requires
 // MUST only be evaluated by the class itself.
 // If you require any additional mutation,
 // then you MUST ensure everything you need in ValidState.
 // You MUST also ensure ValidState in your constructor.
 predicate ValidState()
 predicate GetStringEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The public method to be called by library consumers
 method GetString ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringEnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringEvent 
  && var e' := e as GetStringEvent;
  && e'.input == input 
  && e'.output == output)
 ensures history !in Modifies
 
 predicate GetStringSingleValueEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The public method to be called by library consumers
 method GetStringSingleValue ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringSingleValueEnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringSingleValueEvent 
  && var e' := e as GetStringSingleValueEvent;
  && e'.input == input 
  && e'.output == output)
 ensures history !in Modifies
 
 predicate GetStringUTF8EnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The public method to be called by library consumers
 method GetStringUTF8 ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history 
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringUTF8EnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringUTF8Event 
  && var e' := e as GetStringUTF8Event;
  && e'.input == input 
  && e'.output == output)
 ensures history !in Modifies

}
 datatype Error =
 // Local Error structures are listed here
 
 // Any dependent models are listed here
 
 // The Collection error is used to collect several errors together
 // This is useful when composing OR logic.
 // Consider the following method:
 // 
 // method FN<I, O>(n:I)
 //   returns (res: Result<O, Types.Error>)
 //   ensures A(I).Success? ==> res.Success?
 //   ensures B(I).Success? ==> res.Success?
 //   ensures A(I).Failure? && B(I).Failure? ==> res.Failure?
 // 
 // If either A || B is successful then FN is successful.
 // And if A && B fail then FN will fail.
 // But what information should FN transmit back to the caller?
 // While it may be correct to hide these details from the caller,
 // this can not be the globally correct option.
 // Suppose that A and B can be blocked by different ACLs,
 // and that their representation of I is only eventually consistent.
 // How can the caller distinguish, at a minimum for logging,
 // the difference between the four failure modes?
 // || (!access(A(I)) && !access(B(I)))
 // || (!exit(A(I)) && !exit(B(I)))
 // || (!access(A(I)) && !exit(B(I)))
 // || (!exit(A(I)) && !access(B(I)))
 | CollectionOfErrors(list: seq<Error>, nameonly message: string)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractSimpleTypesSmithyStringService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Histories
 import opened Types = SimpleTypesSmithyStringTypes
 import Operations : AbstractSimpleTypesSmithyStringOperations
 function method DefaultSimpleStringConfig(): SimpleStringConfig
 method SimpleString(config: SimpleStringConfig := DefaultSimpleStringConfig())
 returns (res: Result<SimpleStringClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && res.value.ValidState()

 class SimpleStringClient extends ISimpleTypesStringClient
 {
 constructor(config: Operations.InternalConfig)
 requires Operations.ValidInternalConfig?(config)
 ensures
 && ValidState()
 && this.config == config
 const config: Operations.InternalConfig
 predicate ValidState()
 ensures ValidState() ==>
 && Operations.ValidInternalConfig?(config)
 && Modifies == Operations.ModifiesInternalConfig(config)
 predicate GetStringEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 {Operations.GetStringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetString ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringEnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringEvent 
  && var e' := e as GetStringEvent;
  && e'.input == input 
  && e'.output == output)
 {
 output := Operations.GetString(config, input);
 if history != null {
  var event := new GetStringEvent(input, output);
  history.AddEvent(event);
 }
}
 
 predicate GetStringSingleValueEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 {Operations.GetStringSingleValueEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetStringSingleValue ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringSingleValueEnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringSingleValueEvent 
  && var e' := e as GetStringSingleValueEvent;
  && e'.input == input 
  && e'.output == output)
 {
 output := Operations.GetStringSingleValue(config, input);
 if history != null {
  var event := new GetStringSingleValueEvent(input, output);
  history.AddEvent(event);
 }
}
 
 predicate GetStringUTF8EnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 {Operations.GetStringUTF8EnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetStringUTF8 ( input: GetStringInput, ghost history: History? := null )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 requires history !in Modifies
 modifies Modifies , history
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies
 ensures
 && ValidState()
 ensures GetStringUTF8EnsuresPublicly(input, output)
 ensures history != null ==> history.NewEventSuchThat((e: Event) => 
  && e is GetStringUTF8Event 
  && var e' := e as GetStringUTF8Event;
  && e'.input == input 
  && e'.output == output)
 {
 output := Operations.GetStringUTF8(config, input);
 if history != null {
  var event := new GetStringUTF8Event(input, output);
  history.AddEvent(event);
 }
}
 
}
}
 abstract module AbstractSimpleTypesSmithyStringOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleTypesSmithyStringTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetStringEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The private method to be refined by the library developer


 method GetString ( config: InternalConfig , input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetStringEnsuresPublicly(input, output)


 predicate GetStringSingleValueEnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The private method to be refined by the library developer


 method GetStringSingleValue ( config: InternalConfig , input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetStringSingleValueEnsuresPublicly(input, output)


 predicate GetStringUTF8EnsuresPublicly(input: GetStringInput , output: Result<GetStringOutput, Error>)
 // The private method to be refined by the library developer


 method GetStringUTF8 ( config: InternalConfig , input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetStringUTF8EnsuresPublicly(input, output)
}
