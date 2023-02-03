// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../../../../../../Volumes/workplace/ryan-new-world/polymorph/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy"
 module {:extern "Dafny.Simple.Resources.Types" } SimpleResourcesTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 datatype GetResourceDataInput = | GetResourceDataInput (
 nameonly blobValue: Option<seq<uint8>> ,
 nameonly booleanValue: Option<bool> ,
 nameonly stringValue: Option<string> ,
 nameonly integerValue: Option<int32> ,
 nameonly longValue: Option<int64>
 )
 datatype GetResourceDataOutput = | GetResourceDataOutput (
 nameonly blobValue: Option<seq<uint8>> ,
 nameonly booleanValue: Option<bool> ,
 nameonly stringValue: Option<string> ,
 nameonly integerValue: Option<int32> ,
 nameonly longValue: Option<int64>
 )
 datatype GetResourcesInput = | GetResourcesInput (
 nameonly value: Option<string>
 )
 datatype GetResourcesOutput = | GetResourcesOutput (
 nameonly output: ISimpleResource
 )
 class ISimpleResourceCallHistory {
 ghost constructor() {
 GetResourceData := [];
}
 ghost var GetResourceData: seq<DafnyCallEvent<GetResourceDataInput, Result<GetResourceDataOutput, Error>>>
}
 trait {:termination false} ISimpleResource
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
  ghost const History: ISimpleResourceCallHistory
 predicate GetResourceDataEnsuresPublicly(input: GetResourceDataInput, output: Result<GetResourceDataOutput, Error>)
 // The public method to be called by library consumers
 method GetResourceData ( input: GetResourceDataInput )
 returns (output: Result<GetResourceDataOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetResourceData
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetResourceDataEnsuresPublicly(input, output)
 ensures History.GetResourceData == old(History.GetResourceData) + [DafnyCallEvent(input, output)]
 {
 output := GetResourceData' (input);
 History.GetResourceData := History.GetResourceData + [DafnyCallEvent(input, output)];
}
 // The method to implement in the concrete class. 
 method GetResourceData' ( input: GetResourceDataInput )
 returns (output: Result<GetResourceDataOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History}
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetResourceDataEnsuresPublicly(input, output)
 ensures unchanged(History)
 
}
 class ISimpleResourcesClientCallHistory {
 ghost constructor() {
 GetResources := [];
}
 ghost var GetResources: seq<DafnyCallEvent<GetResourcesInput, Result<GetResourcesOutput, Error>>>
}
 trait {:termination false} ISimpleResourcesClient
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
  ghost const History: ISimpleResourcesClientCallHistory
 predicate GetResourcesEnsuresPublicly(input: GetResourcesInput, output: Result<GetResourcesOutput, Error>)
 // The public method to be called by library consumers
 method GetResources ( input: GetResourcesInput )
 returns (output: Result<GetResourcesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetResources
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.output.ValidState()
 && output.value.output.Modifies !! {History}
 && fresh(output.value.output)
 && fresh ( output.value.output.Modifies - Modifies - {History} ) )
 ensures GetResourcesEnsuresPublicly(input, output)
 ensures History.GetResources == old(History.GetResources) + [DafnyCallEvent(input, output)]
 
}
 datatype SimpleResourcesConfig = | SimpleResourcesConfig (
 nameonly name: string
 )
 datatype Error =
 // Local Error structures are listed here
 | SimpleResourceException (
 nameonly message: string
 )
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
 abstract module AbstractSimpleResourcesService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleResourcesTypes
 import Operations : AbstractSimpleResourcesOperations
 function method DefaultSimpleResourcesConfig(): SimpleResourcesConfig
 method SimpleResources(config: SimpleResourcesConfig := DefaultSimpleResourcesConfig())
 returns (res: Result<SimpleResourcesClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()
 class SimpleResourcesClient extends ISimpleResourcesClient
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
 predicate GetResourcesEnsuresPublicly(input: GetResourcesInput, output: Result<GetResourcesOutput, Error>)
 {Operations.GetResourcesEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetResources ( input: GetResourcesInput )
 returns (output: Result<GetResourcesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetResources
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.output.ValidState()
 && output.value.output.Modifies !! {History}
 && fresh(output.value.output)
 && fresh ( output.value.output.Modifies - Modifies - {History} ) )
 ensures GetResourcesEnsuresPublicly(input, output)
 ensures History.GetResources == old(History.GetResources) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GetResources(config, input);
 History.GetResources := History.GetResources + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractSimpleResourcesOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleResourcesTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetResourcesEnsuresPublicly(input: GetResourcesInput, output: Result<GetResourcesOutput, Error>)
 // The private method to be refined by the library developer


 method GetResources ( config: InternalConfig,  input: GetResourcesInput )
 returns (output: Result<GetResourcesOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 && ( output.Success? ==> 
 && output.value.output.ValidState()
 && fresh(output.value.output)
 && fresh ( output.value.output.Modifies - ModifiesInternalConfig(config) ) )
 ensures GetResourcesEnsuresPublicly(input, output)
}
