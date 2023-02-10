// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestHelpers {
  import ExtendableResource
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers

  function method allNone(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := Option.None(),
      booleanValue := Option.None(),
      stringValue := Option.None(),
      integerValue := Option.None(),
      longValue := Option.None()
    )
  }

  method checkNone(
    output: Types.GetResourceDataOutput
  )
  {
    expect Option.None == output.stringValue;
    expect Option.None() == output.blobValue;
    expect Option.None() == output.booleanValue;
    expect Option.None() == output.integerValue;
    expect Option.None() == output.longValue; 
  }  

  function method allSome(): Types.GetResourceDataInput
  {
   Types.GetResourceDataInput(
      blobValue := Option.Some([1]),
      booleanValue := Option.Some(true),
      stringValue := Option.Some("Some"),
      integerValue := Option.Some(1),
      longValue := Option.Some(1)
    )
  }

  method checkSome(
    output: Types.GetResourceDataOutput
  )
  {
    expect Option.Some("Some") == output.stringValue;
    expect Option.Some([1]) == output.blobValue;
    expect Option.Some(true) == output.booleanValue;
    expect Option.Some(1) == output.integerValue;
    expect Option.Some(1) == output.longValue; 
  }

  method CheckModeledError(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    expect actualError == Types.SimpleExtendableResourcesException(
      message := "Hard Coded Exception in src/dafny"
    );
  }

  method CheckMultipleErrors(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    // TypeConversion.FromDafny_CommonError does not handle Collection.
    // As such, even though AlwaysMutlipleErrors correctly returns a Collection in Dafny,
    // the generated .NET code botches the conversion,
    // and lumps it as an Opaue Exception.
    // TODO:
    // Once https://github.com/awslabs/polymorph/pull/136 is resolved/merged
    // and smithy-dotnet handles Collections, replace
    // expect actualError.Opaque? with commented out expect,
    // and remove this comment.
    expect actualError.Opaque?;
    // expect actualError.Collection?
    //   && |actualError.list| == 1
    //   && actualError.list[0].SimpleExtendableResourcesException?
    //   && actualError.list[0].message == "Hard Coded Modeled Exception in Collection";
  }

  method CheckDafnyMultipleErrors(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    // TypeConversion.FromDafny_CommonError does not handle Collection.
    // As such, even though AlwaysMutlipleErrors correctly returns a Collection in Dafny,
    // the generated .NET code botches the conversion,
    // and lumps it as an Opaue Exception.
    // TODO:
    // Once https://github.com/awslabs/polymorph/pull/136 is resolved/merged
    // and smithy-dotnet handles Collections, replace
    // expect actualError.Opaque? with commented out expect,
    // and remove this comment.
    // expect actualError.Opaque?;
    expect actualError.Collection?
      && |actualError.list| == 1
      && actualError.list[0].SimpleExtendableResourcesException?
      && actualError.list[0].message == "Hard Coded Modeled Exception in Collection";
  }
  
  method CheckOpaqueError(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    expect actualError.Opaque?
      // Opaque Errors SHOULD NOT be thrown by Dafny source.
      // (At least) Smithy-dotnet expects the obj
      // to be an Exception that it can throw.
      // It is a PITA to write a class in Dafny
      // that maps to an Exception in every runtime,
      // so we are NOT going to do that.
      // Therefore, we cannot constrain/test the value of obj
      // with pure Dafny.
      && !(actualError.obj is ExtendableResource.OpaqueMessage);
      // For the curious,
      // in .NET, the obj will be a Native OpaqueError,
      // with the message:
      // "Opaque obj is not an Exception."
      // But we cannot test that here,
      // as we cannot call the TypeConversion method
      // from inside Dafny.
  }

  method CheckDafnyOpaqueError(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    expect actualError.Opaque?
      && (actualError.obj is ExtendableResource.OpaqueMessage);
  }
  
  method {:extern "Simple.Extendable.Resources.NativeResource", "DafnyFactory"} DafnyFactory(
  ) returns (
    output: Types.IExtendableResource
  )
    ensures output.ValidState() && fresh(output.History) && fresh(output.Modifies)  
}
