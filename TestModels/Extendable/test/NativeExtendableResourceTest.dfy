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
    TestSomeGetResourceData(resource);
    TestNoneGetResourceData(resource);
    TestAlwaysModeledError(resource);
    TestAlwaysMultipleErrors(resource);
    TestAlwaysOpaqueError(resource);
    TestNoneAlwaysOpaqueError(resource);
  }

  method TestSomeGetResourceData(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var dataInput := allSome();
    var dataOutput :- expect resource.GetResourceData(dataInput);
    checkSome(dataOutput, ExtendableResource.DEFAULT_RESOURCE_NAME);
  }

  method TestNoneGetResourceData(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var dataInput := allNone();
    var dataOutput :- expect resource.GetResourceData(dataInput);
    checkNone(dataOutput, ExtendableResource.DEFAULT_RESOURCE_NAME);
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
    var errorOutput := resource.AlwaysModeledError(errorInput);
    CheckModeledError(errorOutput);
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
    var errorOutput := resource.AlwaysMultipleErrors(errorInput);
    CheckMultipleErrors(errorOutput);
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
    var errorOutput := resource.AlwaysOpaqueError(errorInput);
    expect errorOutput.Failure?;
    var actualError := errorOutput.error;
    expect actualError.Opaque?;
    // The Value of actualError SHOULD be
    // OpaqueError:
    // Message: "OpaqueError:"
    // Obj: "Exception(".NET Hard Coded Exception")"
    // Which can be checked by uncommenting the print statement below
    // print("\n\t Dafny Opaque Error");
    // print("\n\t");
    // print(actualError);
    // print("\n");
  }

   method TestNoneAlwaysOpaqueError(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := None()
    );
    var errorOutput := resource.AlwaysOpaqueError(errorInput);
    CheckOpaqueError(errorOutput);
  }
}
