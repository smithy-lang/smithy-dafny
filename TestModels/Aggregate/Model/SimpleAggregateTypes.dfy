// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../DafnyLib/std/src/Index.dfy"
 module {:extern "Dafny.Simple.Aggregate.Types" } SimpleAggregateTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 datatype Deeply = | Deeply (
 nameonly nested: Option<Nested>
 )
 datatype GetAggregateInput = | GetAggregateInput (
 nameonly simpleStringList: Option<SimpleStringList> ,
 nameonly structureList: Option<StructureList> ,
 nameonly SimpleStringMap: Option<SimpleStringMap> ,
 nameonly SimpleIntegerMap: Option<SimpleIntegerMap> ,
 nameonly very: Option<Deeply>
 )
 datatype GetAggregateOutput = | GetAggregateOutput (
 nameonly simpleStringList: Option<SimpleStringList> ,
 nameonly structureList: Option<StructureList> ,
 nameonly SimpleStringMap: Option<SimpleStringMap> ,
 nameonly SimpleIntegerMap: Option<SimpleIntegerMap> ,
 nameonly very: Option<Deeply>
 )
 datatype Nested = | Nested (
 nameonly value: Option<string>
 )
 class ISimpleAggregateClientCallHistory {
 ghost constructor() {
 GetAggregate := [];
}
 ghost var GetAggregate: seq<DafnyCallEvent<GetAggregateInput, Result<GetAggregateOutput, Error>>>
}
 trait {:termination false} ISimpleAggregateClient
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
  ghost const History: ISimpleAggregateClientCallHistory
 predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
 // The public method to be called by library consumers
 method GetAggregate ( input: GetAggregateInput )
 returns (output: Result<GetAggregateOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetAggregate
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetAggregateEnsuresPublicly(input, output)
 ensures History.GetAggregate == old(History.GetAggregate) + [DafnyCallEvent(input, output)]
 
}
 datatype SimpleAggregateConfig = | SimpleAggregateConfig (
 
 )
 type SimpleIntegerMap = map<string, int32>
 type SimpleStringList = seq<string>
 type SimpleStringMap = map<string, string>
 type StructureList = seq<StructureListElement>
 datatype StructureListElement = | StructureListElement (
 nameonly s: Option<string> ,
 nameonly i: Option<int32>
 )
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
 abstract module AbstractSimpleAggregateService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleAggregateTypes
 import Operations : AbstractSimpleAggregateOperations
 function method DefaultSimpleAggregateConfig(): SimpleAggregateConfig
 method SimpleAggregate(config: SimpleAggregateConfig := DefaultSimpleAggregateConfig())
 returns (res: Result<SimpleAggregateClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
 class SimpleAggregateClient extends ISimpleAggregateClient
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
 predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
 {Operations.GetAggregateEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetAggregate ( input: GetAggregateInput )
 returns (output: Result<GetAggregateOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetAggregate
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetAggregateEnsuresPublicly(input, output)
 ensures History.GetAggregate == old(History.GetAggregate) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GetAggregate(config, input);
 History.GetAggregate := History.GetAggregate + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractSimpleAggregateOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleAggregateTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetAggregateEnsuresPublicly(input: GetAggregateInput, output: Result<GetAggregateOutput, Error>)
 // The private method to be refined by the library developer


 method GetAggregate ( config: InternalConfig,  input: GetAggregateInput )
 returns (output: Result<GetAggregateOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetAggregateEnsuresPublicly(input, output)
}
