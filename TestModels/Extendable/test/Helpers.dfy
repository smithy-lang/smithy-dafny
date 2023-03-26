// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module TestHelpers {
  import ExtendableResource
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers

  function method allNone(): Types.GetExtendableResourceDataInput
  {
   Types.GetExtendableResourceDataInput(
      blobValue := None,
      booleanValue := None,
      stringValue := None,
      integerValue := None,
      longValue := None
    )
  }

  method checkNone(
    output: Types.GetExtendableResourceDataOutput,
    name: string
  )
  {
    expect output.stringValue == Some(name);
    expect output.blobValue.None?;
    expect output.booleanValue.None?;
    expect output.integerValue.None?;
    expect output.longValue.None?;
  }  

  function method allSome(): Types.GetExtendableResourceDataInput
  {
   Types.GetExtendableResourceDataInput(
      blobValue := Some([1]),
      booleanValue := Some(true),
      stringValue := Some("Some"),
      integerValue := Some(1),
      longValue := Some(1)
    )
  }

  method checkSome(
    output: Types.GetExtendableResourceDataOutput,
    name: string
  )
  {
    expect Some("Some"+ " " + name) == output.stringValue;
    expect Some([1]) == output.blobValue;
    expect Some(true) == output.booleanValue;
    expect Some(1) == output.integerValue;
    expect Some(1) == output.longValue; 
  }

  method CheckModeledError(
    errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>
  )
  {
    expect errorOutput.Failure?;
    var actualError := errorOutput.error;
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
    expect actualError.CollectionOfErrors?
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
}
