// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "./Helpers.dfy"

module NativeExtendableResourceTest {
  import ExtendableResource
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers
  import opened TestHelpers

  method {:test} TestNativeResource()
  {
    var resource: Types.IExtendableResource := DafnyFactory();
    TestAlwaysModeledError(resource);
    TestAlwaysMultipleErrors(resource);
    TestAlwaysOpaqueError(resource);
  }

  method TestAlwaysModeledError(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysModeledError(errorInput);
    expect errorOutput.Failure?;
    var actualError := errorOutput.PropagateFailure<Types.GetExtendableResourceErrorsOutput>().error;
    expect actualError == Types.SimpleExtendableResourcesException(message := "Hard Coded Exception in src/dafny");
  }

  method TestAlwaysMultipleErrors(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysMultipleErrors(errorInput);
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

  method TestAlwaysOpaqueError(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysOpaqueError(errorInput);
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
}  
