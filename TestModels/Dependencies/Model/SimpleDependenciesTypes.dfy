// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../dafny-dependencies/StandardLibrary/src/Index.dfy"
 include "../../Constraints/src/Index.dfy"
 include "../../Extendable/src/Index.dfy"
 include "../../Resource/src/Index.dfy"
 module {:extern "Dafny.Simple.Dependencies.Types" } SimpleDependenciesTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import SimpleConstraintsTypes
 import SimpleExtendableResourcesTypes
 import SimpleResourcesTypes
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 class ISimpleDependenciesClientCallHistory {
 ghost constructor() {
 GetSimpleResource := [];
 UseSimpleResource := [];
 UseLocalConstraintsService := [];
 UseLocalExtendableResource := [];
 LocalExtendableResourceAlwaysModeledError := [];
 LocalExtendableResourceAlwaysMultipleErrors := [];
 LocalExtendableResourceAlwaysNativeError := [];
}
 ghost var GetSimpleResource: seq<DafnyCallEvent<SimpleResourcesTypes.GetResourcesInput, Result<SimpleResourcesTypes.GetResourcesOutput, Error>>>
 ghost var UseSimpleResource: seq<DafnyCallEvent<UseSimpleResourceInput, Result<SimpleResourcesTypes.GetResourceDataOutput, Error>>>
 ghost var UseLocalConstraintsService: seq<DafnyCallEvent<SimpleConstraintsTypes.GetConstraintsInput, Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>>>
 ghost var UseLocalExtendableResource: seq<DafnyCallEvent<SimpleExtendableResourcesTypes.GetExtendableResourceDataInput, Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>>>
 ghost var LocalExtendableResourceAlwaysModeledError: seq<DafnyCallEvent<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput, Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>>>
 ghost var LocalExtendableResourceAlwaysMultipleErrors: seq<DafnyCallEvent<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput, Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>>>
 ghost var LocalExtendableResourceAlwaysNativeError: seq<DafnyCallEvent<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput, Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>>>
}
 trait {:termination false} ISimpleDependenciesClient
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
  ghost const History: ISimpleDependenciesClientCallHistory
 predicate GetSimpleResourceEnsuresPublicly(input: SimpleResourcesTypes.GetResourcesInput , output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
 // The public method to be called by library consumers
 method GetSimpleResource ( input: SimpleResourcesTypes.GetResourcesInput )
 returns (output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetSimpleResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.output.ValidState()
 && output.value.output.Modifies !! {History}
 && fresh(output.value.output)
 && fresh ( output.value.output.Modifies - Modifies - {History} ) )
 ensures GetSimpleResourceEnsuresPublicly(input, output)
 ensures History.GetSimpleResource == old(History.GetSimpleResource) + [DafnyCallEvent(input, output)]
 
 predicate UseSimpleResourceEnsuresPublicly(input: UseSimpleResourceInput , output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 // The public method to be called by library consumers
 method UseSimpleResource ( input: UseSimpleResourceInput )
 returns (output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 requires
 && ValidState()
 && input.value.ValidState()
 && input.value.Modifies !! {History}
 modifies Modifies - {History} ,
 input.value.Modifies ,
 History`UseSimpleResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.value.Modifies
 ensures
 && ValidState()
 ensures UseSimpleResourceEnsuresPublicly(input, output)
 ensures History.UseSimpleResource == old(History.UseSimpleResource) + [DafnyCallEvent(input, output)]
 
 predicate UseLocalConstraintsServiceEnsuresPublicly(input: SimpleConstraintsTypes.GetConstraintsInput , output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 // The public method to be called by library consumers
 method UseLocalConstraintsService ( input: SimpleConstraintsTypes.GetConstraintsInput )
 returns (output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UseLocalConstraintsService
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UseLocalConstraintsServiceEnsuresPublicly(input, output)
 ensures History.UseLocalConstraintsService == old(History.UseLocalConstraintsService) + [DafnyCallEvent(input, output)]
 
 predicate UseLocalExtendableResourceEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput , output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 // The public method to be called by library consumers
 method UseLocalExtendableResource ( input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput )
 returns (output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UseLocalExtendableResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UseLocalExtendableResourceEnsuresPublicly(input, output)
 ensures History.UseLocalExtendableResource == old(History.UseLocalExtendableResource) + [DafnyCallEvent(input, output)]
 
 predicate LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysModeledError ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysModeledError
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysModeledError == old(History.LocalExtendableResourceAlwaysModeledError) + [DafnyCallEvent(input, output)]
 
 predicate LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysMultipleErrors ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysMultipleErrors
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysMultipleErrors == old(History.LocalExtendableResourceAlwaysMultipleErrors) + [DafnyCallEvent(input, output)]
 
 predicate LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysNativeError ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysNativeError
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysNativeError == old(History.LocalExtendableResourceAlwaysNativeError) + [DafnyCallEvent(input, output)]
 
}
 datatype SimpleDependenciesConfig = | SimpleDependenciesConfig (
 nameonly simpleResourcesConfig: Option<SimpleResourcesTypes.SimpleResourcesConfig> ,
 nameonly simpleConstraintsServiceReference: Option<SimpleConstraintsTypes.ISimpleConstraintsClient> ,
 nameonly extendableResourceReference: Option<SimpleExtendableResourcesTypes.IExtendableResource> ,
 nameonly specialString: Option<SimpleConstraintsTypes.MyString>
 )
 datatype UseSimpleResourceInput = | UseSimpleResourceInput (
 nameonly value: SimpleResourcesTypes.ISimpleResource ,
 nameonly input: SimpleResourcesTypes.GetResourceDataInput
 )
 datatype Error =
 // Local Error structures are listed here
 
 // Any dependent models are listed here
 | SimpleConstraints(SimpleConstraints: SimpleConstraintsTypes.Error)
 | SimpleExtendableResources(SimpleExtendableResources: SimpleExtendableResourcesTypes.Error)
 | SimpleResources(SimpleResources: SimpleResourcesTypes.Error)
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
 | CollectionOfErrors(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractSimpleDependenciesService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleDependenciesTypes
 import Operations : AbstractSimpleDependenciesOperations
 function method DefaultSimpleDependenciesConfig(): SimpleDependenciesConfig
 method SimpleDependencies(config: SimpleDependenciesConfig := DefaultSimpleDependenciesConfig())
 returns (res: Result<SimpleDependenciesClient, Error>)
 requires config.simpleConstraintsServiceReference.Some? ==>
 config.simpleConstraintsServiceReference.value.ValidState()
 requires config.extendableResourceReference.Some? ==>
 config.extendableResourceReference.value.ValidState()
 modifies if config.simpleConstraintsServiceReference.Some? then 
 config.simpleConstraintsServiceReference.value.Modifies
 else {}
 modifies if config.extendableResourceReference.Some? then 
 config.extendableResourceReference.value.Modifies
 else {}
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies
 - ( if config.simpleConstraintsServiceReference.Some? then 
 config.simpleConstraintsServiceReference.value.Modifies
 else {}
 ) - ( if config.extendableResourceReference.Some? then 
 config.extendableResourceReference.value.Modifies
 else {}
 ) )
 && fresh(res.value.History)
 && res.value.ValidState()
 ensures config.simpleConstraintsServiceReference.Some? ==>
 config.simpleConstraintsServiceReference.value.ValidState()
 ensures config.extendableResourceReference.Some? ==>
 config.extendableResourceReference.value.ValidState()

 class SimpleDependenciesClient extends ISimpleDependenciesClient
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
 predicate GetSimpleResourceEnsuresPublicly(input: SimpleResourcesTypes.GetResourcesInput , output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
 {Operations.GetSimpleResourceEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetSimpleResource ( input: SimpleResourcesTypes.GetResourcesInput )
 returns (output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetSimpleResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 && ( output.Success? ==> 
 && output.value.output.ValidState()
 && output.value.output.Modifies !! {History}
 && fresh(output.value.output)
 && fresh ( output.value.output.Modifies - Modifies - {History} ) )
 ensures GetSimpleResourceEnsuresPublicly(input, output)
 ensures History.GetSimpleResource == old(History.GetSimpleResource) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GetSimpleResource(config, input);
 History.GetSimpleResource := History.GetSimpleResource + [DafnyCallEvent(input, output)];
}
 
 predicate UseSimpleResourceEnsuresPublicly(input: UseSimpleResourceInput , output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 {Operations.UseSimpleResourceEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method UseSimpleResource ( input: UseSimpleResourceInput )
 returns (output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 requires
 && ValidState()
 && input.value.ValidState()
 && input.value.Modifies !! {History}
 modifies Modifies - {History} ,
 input.value.Modifies ,
 History`UseSimpleResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History} ,
 input.value.Modifies
 ensures
 && ValidState()
 ensures UseSimpleResourceEnsuresPublicly(input, output)
 ensures History.UseSimpleResource == old(History.UseSimpleResource) + [DafnyCallEvent(input, output)]
 {
 output := Operations.UseSimpleResource(config, input);
 History.UseSimpleResource := History.UseSimpleResource + [DafnyCallEvent(input, output)];
}
 
 predicate UseLocalConstraintsServiceEnsuresPublicly(input: SimpleConstraintsTypes.GetConstraintsInput , output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 {Operations.UseLocalConstraintsServiceEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method UseLocalConstraintsService ( input: SimpleConstraintsTypes.GetConstraintsInput )
 returns (output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UseLocalConstraintsService
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UseLocalConstraintsServiceEnsuresPublicly(input, output)
 ensures History.UseLocalConstraintsService == old(History.UseLocalConstraintsService) + [DafnyCallEvent(input, output)]
 {
 output := Operations.UseLocalConstraintsService(config, input);
 History.UseLocalConstraintsService := History.UseLocalConstraintsService + [DafnyCallEvent(input, output)];
}
 
 predicate UseLocalExtendableResourceEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput , output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 {Operations.UseLocalExtendableResourceEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method UseLocalExtendableResource ( input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput )
 returns (output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`UseLocalExtendableResource
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures UseLocalExtendableResourceEnsuresPublicly(input, output)
 ensures History.UseLocalExtendableResource == old(History.UseLocalExtendableResource) + [DafnyCallEvent(input, output)]
 {
 output := Operations.UseLocalExtendableResource(config, input);
 History.UseLocalExtendableResource := History.UseLocalExtendableResource + [DafnyCallEvent(input, output)];
}
 
 predicate LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 {Operations.LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysModeledError ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysModeledError
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysModeledError == old(History.LocalExtendableResourceAlwaysModeledError) + [DafnyCallEvent(input, output)]
 {
 output := Operations.LocalExtendableResourceAlwaysModeledError(config, input);
 History.LocalExtendableResourceAlwaysModeledError := History.LocalExtendableResourceAlwaysModeledError + [DafnyCallEvent(input, output)];
}
 
 predicate LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 {Operations.LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysMultipleErrors ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysMultipleErrors
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysMultipleErrors == old(History.LocalExtendableResourceAlwaysMultipleErrors) + [DafnyCallEvent(input, output)]
 {
 output := Operations.LocalExtendableResourceAlwaysMultipleErrors(config, input);
 History.LocalExtendableResourceAlwaysMultipleErrors := History.LocalExtendableResourceAlwaysMultipleErrors + [DafnyCallEvent(input, output)];
}
 
 predicate LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 {Operations.LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method LocalExtendableResourceAlwaysNativeError ( input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`LocalExtendableResourceAlwaysNativeError
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input, output)
 ensures History.LocalExtendableResourceAlwaysNativeError == old(History.LocalExtendableResourceAlwaysNativeError) + [DafnyCallEvent(input, output)]
 {
 output := Operations.LocalExtendableResourceAlwaysNativeError(config, input);
 History.LocalExtendableResourceAlwaysNativeError := History.LocalExtendableResourceAlwaysNativeError + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractSimpleDependenciesOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleDependenciesTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetSimpleResourceEnsuresPublicly(input: SimpleResourcesTypes.GetResourcesInput , output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
 // The private method to be refined by the library developer


 method GetSimpleResource ( config: InternalConfig , input: SimpleResourcesTypes.GetResourcesInput )
 returns (output: Result<SimpleResourcesTypes.GetResourcesOutput, Error>)
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
 ensures GetSimpleResourceEnsuresPublicly(input, output)


 predicate UseSimpleResourceEnsuresPublicly(input: UseSimpleResourceInput , output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 // The private method to be refined by the library developer


 method UseSimpleResource ( config: InternalConfig , input: UseSimpleResourceInput )
 returns (output: Result<SimpleResourcesTypes.GetResourceDataOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 && input.value.ValidState()
 modifies ModifiesInternalConfig(config) ,
 input.value.Modifies
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config) ,
 input.value.Modifies
 ensures
 && ValidInternalConfig?(config)
 ensures UseSimpleResourceEnsuresPublicly(input, output)


 predicate UseLocalConstraintsServiceEnsuresPublicly(input: SimpleConstraintsTypes.GetConstraintsInput , output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 // The private method to be refined by the library developer


 method UseLocalConstraintsService ( config: InternalConfig , input: SimpleConstraintsTypes.GetConstraintsInput )
 returns (output: Result<SimpleConstraintsTypes.GetConstraintsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UseLocalConstraintsServiceEnsuresPublicly(input, output)


 predicate UseLocalExtendableResourceEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput , output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 // The private method to be refined by the library developer


 method UseLocalExtendableResource ( config: InternalConfig , input: SimpleExtendableResourcesTypes.GetExtendableResourceDataInput )
 returns (output: Result<SimpleExtendableResourcesTypes.UseExtendableResourceOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures UseLocalExtendableResourceEnsuresPublicly(input, output)


 predicate LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The private method to be refined by the library developer


 method LocalExtendableResourceAlwaysModeledError ( config: InternalConfig , input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures LocalExtendableResourceAlwaysModeledErrorEnsuresPublicly(input, output)


 predicate LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The private method to be refined by the library developer


 method LocalExtendableResourceAlwaysMultipleErrors ( config: InternalConfig , input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures LocalExtendableResourceAlwaysMultipleErrorsEnsuresPublicly(input, output)


 predicate LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput , output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 // The private method to be refined by the library developer


 method LocalExtendableResourceAlwaysNativeError ( config: InternalConfig , input: SimpleExtendableResourcesTypes.GetExtendableResourceErrorsInput )
 returns (output: Result<SimpleExtendableResourcesTypes.GetExtendableResourceErrorsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures LocalExtendableResourceAlwaysNativeErrorEnsuresPublicly(input, output)
}
