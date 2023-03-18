// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
include "../../../../../../../../Volumes/workplace/ryan-new-world/polymorph/TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy"
 module {:extern "Dafny.Simple.Constraints.Types" } SimpleConstraintsTypes
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 // Generic helpers for verification of mock/unit tests.
 datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O)
 
 // Begin Generated Types
 
 type Alphabetic = string
 type BlobLessThanOrEqualToTen = x: seq<uint8> | IsValid_BlobLessThanOrEqualToTen(x) witness *
 predicate method IsValid_BlobLessThanOrEqualToTen(x: seq<uint8>) {
 (  |x| <= 10 )
}
 datatype ComplexListElement = | ComplexListElement (
 nameonly value: Option<string> ,
 nameonly blob: Option<seq<uint8>>
 )
 datatype GetConstraintsInput = | GetConstraintsInput (
 nameonly MyString: Option<MyString> ,
 nameonly NonEmptyString: Option<NonEmptyString> ,
 nameonly StringLessThanOrEqualToTen: Option<StringLessThanOrEqualToTen> ,
 nameonly MyBlob: Option<MyBlob> ,
 nameonly NonEmptyBlob: Option<NonEmptyBlob> ,
 nameonly BlobLessThanOrEqualToTen: Option<BlobLessThanOrEqualToTen> ,
 nameonly MyList: Option<MyList> ,
 nameonly NonEmptyList: Option<NonEmptyList> ,
 nameonly ListLessThanOrEqualToTen: Option<ListLessThanOrEqualToTen> ,
 nameonly MyMap: Option<MyMap> ,
 nameonly NonEmptyMap: Option<NonEmptyMap> ,
 nameonly MapLessThanOrEqualToTen: Option<MapLessThanOrEqualToTen> ,
 nameonly Alphabetic: Option<Alphabetic> ,
 nameonly OneToTen: Option<OneToTen> ,
 nameonly GreaterThanOne: Option<GreaterThanOne> ,
 nameonly LessThanTen: Option<LessThanTen> ,
 nameonly MyUniqueList: Option<MyUniqueList> ,
 nameonly MyComplexUniqueList: Option<MyComplexUniqueList> ,
 nameonly MyUtf8Bytes: Option<Utf8Bytes> ,
 nameonly MyListOfUtf8Bytes: Option<ListOfUtf8Bytes>
 )
 datatype GetConstraintsOutput = | GetConstraintsOutput (
 nameonly MyString: Option<MyString> ,
 nameonly NonEmptyString: Option<NonEmptyString> ,
 nameonly StringLessThanOrEqualToTen: Option<StringLessThanOrEqualToTen> ,
 nameonly MyBlob: Option<MyBlob> ,
 nameonly NonEmptyBlob: Option<NonEmptyBlob> ,
 nameonly BlobLessThanOrEqualToTen: Option<BlobLessThanOrEqualToTen> ,
 nameonly MyList: Option<MyList> ,
 nameonly NonEmptyList: Option<NonEmptyList> ,
 nameonly ListLessThanOrEqualToTen: Option<ListLessThanOrEqualToTen> ,
 nameonly MyMap: Option<MyMap> ,
 nameonly NonEmptyMap: Option<NonEmptyMap> ,
 nameonly MapLessThanOrEqualToTen: Option<MapLessThanOrEqualToTen> ,
 nameonly Alphabetic: Option<Alphabetic> ,
 nameonly OneToTen: Option<OneToTen> ,
 nameonly GreaterThanOne: Option<GreaterThanOne> ,
 nameonly LessThanTen: Option<LessThanTen> ,
 nameonly MyUniqueList: Option<MyUniqueList> ,
 nameonly MyComplexUniqueList: Option<MyComplexUniqueList> ,
 nameonly MyUtf8Bytes: Option<Utf8Bytes> ,
 nameonly MyListOfUtf8Bytes: Option<ListOfUtf8Bytes>
 )
 type GreaterThanOne = x: int32 | IsValid_GreaterThanOne(x) witness *
 predicate method IsValid_GreaterThanOne(x: int32) {
 ( 1 <= x  )
}
 type LessThanTen = x: int32 | IsValid_LessThanTen(x) witness *
 predicate method IsValid_LessThanTen(x: int32) {
 (  x <= 10 )
}
 type ListLessThanOrEqualToTen = x: seq<string> | IsValid_ListLessThanOrEqualToTen(x) witness *
 predicate method IsValid_ListLessThanOrEqualToTen(x: seq<string>) {
 (  |x| <= 10 )
}
 type ListOfUtf8Bytes = seq<Utf8Bytes>
 type MapLessThanOrEqualToTen = x: map<string, string> | IsValid_MapLessThanOrEqualToTen(x) witness *
 predicate method IsValid_MapLessThanOrEqualToTen(x: map<string, string>) {
 (  |x| <= 10 )
}
 type MyBlob = x: seq<uint8> | IsValid_MyBlob(x) witness *
 predicate method IsValid_MyBlob(x: seq<uint8>) {
 ( 1 <= |x| <= 10 )
}
 type MyComplexUniqueList = seq<ComplexListElement>
 type MyList = x: seq<string> | IsValid_MyList(x) witness *
 predicate method IsValid_MyList(x: seq<string>) {
 ( 1 <= |x| <= 10 )
}
 type MyMap = x: map<string, string> | IsValid_MyMap(x) witness *
 predicate method IsValid_MyMap(x: map<string, string>) {
 ( 1 <= |x| <= 10 )
}
 type MyString = x: string | IsValid_MyString(x) witness *
 predicate method IsValid_MyString(x: string) {
 ( 1 <= |x| <= 10 )
}
 type MyUniqueList = seq<string>
 type NonEmptyBlob = x: seq<uint8> | IsValid_NonEmptyBlob(x) witness *
 predicate method IsValid_NonEmptyBlob(x: seq<uint8>) {
 ( 1 <= |x|  )
}
 type NonEmptyList = x: seq<string> | IsValid_NonEmptyList(x) witness *
 predicate method IsValid_NonEmptyList(x: seq<string>) {
 ( 1 <= |x|  )
}
 type NonEmptyMap = x: map<string, string> | IsValid_NonEmptyMap(x) witness *
 predicate method IsValid_NonEmptyMap(x: map<string, string>) {
 ( 1 <= |x|  )
}
 type NonEmptyString = x: string | IsValid_NonEmptyString(x) witness *
 predicate method IsValid_NonEmptyString(x: string) {
 ( 1 <= |x|  )
}
 type OneToTen = x: int32 | IsValid_OneToTen(x) witness *
 predicate method IsValid_OneToTen(x: int32) {
 ( 1 <= x <= 10 )
}
 class ISimpleConstraintsClientCallHistory {
 ghost constructor() {
 GetConstraints := [];
}
 ghost var GetConstraints: seq<DafnyCallEvent<GetConstraintsInput, Result<GetConstraintsOutput, Error>>>
}
 trait {:termination false} ISimpleConstraintsClient
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
  ghost const History: ISimpleConstraintsClientCallHistory
 predicate GetConstraintsEnsuresPublicly(input: GetConstraintsInput , output: Result<GetConstraintsOutput, Error>)
 // The public method to be called by library consumers
 method GetConstraints ( input: GetConstraintsInput )
 returns (output: Result<GetConstraintsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetConstraints
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetConstraintsEnsuresPublicly(input, output)
 ensures History.GetConstraints == old(History.GetConstraints) + [DafnyCallEvent(input, output)]
 
}
 datatype SimpleConstraintsConfig = | SimpleConstraintsConfig (
 
 )
 type StringLessThanOrEqualToTen = x: string | IsValid_StringLessThanOrEqualToTen(x) witness *
 predicate method IsValid_StringLessThanOrEqualToTen(x: string) {
 (  |x| <= 10 )
}
 type Utf8Bytes = ValidUTF8Bytes
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
 | CollectionOfErrors(list: seq<Error>)
 // The Opaque error, used for native, extern, wrapped or unknown errors
 | Opaque(obj: object)
 type OpaqueError = e: Error | e.Opaque? witness *
}
 abstract module AbstractSimpleConstraintsService
 {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleConstraintsTypes
 import Operations : AbstractSimpleConstraintsOperations
 function method DefaultSimpleConstraintsConfig(): SimpleConstraintsConfig
 method SimpleConstraints(config: SimpleConstraintsConfig := DefaultSimpleConstraintsConfig())
 returns (res: Result<SimpleConstraintsClient, Error>)
 ensures res.Success? ==> 
 && fresh(res.value)
 && fresh(res.value.Modifies)
 && fresh(res.value.History)
 && res.value.ValidState()

 class SimpleConstraintsClient extends ISimpleConstraintsClient
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
 predicate GetConstraintsEnsuresPublicly(input: GetConstraintsInput , output: Result<GetConstraintsOutput, Error>)
 {Operations.GetConstraintsEnsuresPublicly(input, output)}
 // The public method to be called by library consumers
 method GetConstraints ( input: GetConstraintsInput )
 returns (output: Result<GetConstraintsOutput, Error>)
 requires
 && ValidState()
 modifies Modifies - {History} ,
 History`GetConstraints
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases Modifies - {History}
 ensures
 && ValidState()
 ensures GetConstraintsEnsuresPublicly(input, output)
 ensures History.GetConstraints == old(History.GetConstraints) + [DafnyCallEvent(input, output)]
 {
 output := Operations.GetConstraints(config, input);
 History.GetConstraints := History.GetConstraints + [DafnyCallEvent(input, output)];
}
 
}
}
 abstract module AbstractSimpleConstraintsOperations {
 import opened Wrappers
 import opened StandardLibrary.UInt
 import opened UTF8
 import opened Types = SimpleConstraintsTypes
 type InternalConfig
 predicate ValidInternalConfig?(config: InternalConfig)
 function ModifiesInternalConfig(config: InternalConfig): set<object>
 predicate GetConstraintsEnsuresPublicly(input: GetConstraintsInput , output: Result<GetConstraintsOutput, Error>)
 // The private method to be refined by the library developer


 method GetConstraints ( config: InternalConfig , input: GetConstraintsInput )
 returns (output: Result<GetConstraintsOutput, Error>)
 requires
 && ValidInternalConfig?(config)
 modifies ModifiesInternalConfig(config)
 // Dafny will skip type parameters when generating a default decreases clause.
 decreases ModifiesInternalConfig(config)
 ensures
 && ValidInternalConfig?(config)
 ensures GetConstraintsEnsuresPublicly(input, output)
}
