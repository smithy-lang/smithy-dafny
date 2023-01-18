// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../smithy-polymorph/lib/std/src/Index.dfy"
 module {:extern "Dafny.Example.Simpletypes.Types" } ExampleSimpletypesTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 datatype EmptyConfig = | EmptyConfig (
 
 )
 datatype GetStringInput = | GetStringInput (
 nameonly stringValue: Option<string>
 )
 datatype GetStringOutput = | GetStringOutput (
 nameonly result: Option<string>
 )
 class ISimpleTypesServiceClientCallHistory {
 ghost constructor() {
 GetString := [];
}
 ghost var GetString: seq<DafnyCallEvent<GetStringInput, Result<GetStringOutput, Error>>>
}
 trait {:termination false} ISimpleTypesServiceClient
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
 ensures ValidState() ==> History in Modifies
  ghost const History: ISimpleTypesServiceClientCallHistory
 predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
 // The public method to be called by library consumers
 method GetString ( input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetString
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetStringEnsuresPublicly(input, output)
 ensures History.GetString == old(History.GetString) + [DafnyCallEvent(input, output)]
 
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
 | Collection(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractExampleSimpletypesService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ExampleSimpletypesTypes
 import Operations : AbstractExampleSimpletypesOperations
 function method DefaultEmptyConfig(): EmptyConfig
 method SimpleTypes(config: EmptyConfig := DefaultEmptyConfig())
 returns (res: Result<SimpleTypesClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
 class SimpleTypesClient extends ISimpleTypesServiceClient
 {
 constructor(config: Operations.InternalConfig)
 requires Operations.ValidInternalConfig?(config)
 ensures
 && ValidState()
 && fresh(History)
 && this.config == config
 const config: Operations.InternalConfig
 predicate ValidState()
 ensures ValidState() ==>
 && Operations.ValidInternalConfig?(config)
 && History !in Operations.ModifiesInternalConfig(config)
 && Modifies == Operations.ModifiesInternalConfig(config) + {History}
 predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
 {Operations.GetStringEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetString ( input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetString
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetStringEnsuresPublicly(input, output)
 ensures History.GetString == old(History.GetString) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GetString(config, input);
 History.GetString := History.GetString + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractExampleSimpletypesOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = ExampleSimpletypesTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetStringEnsuresPublicly(input: GetStringInput, output: Result<GetStringOutput, Error>)
 // The private method to be refined by the library developer


 method GetString ( config: InternalConfig,  input: GetStringInput )
 returns (output: Result<GetStringOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetStringEnsuresPublicly(input, output)
}
