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
  }

  method TestSomeGetResourceData(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var dataInput: Types.GetResourceDataInput := allSome();
    var dataOutput: Types.GetResourceDataOutput :- expect resource.GetResourceData(dataInput);
    checkSome(dataOutput, ExtendableResource.DEFAULT_RESOURCE_NAME);
  }

  method TestNoneGetResourceData(
    resource: Types.IExtendableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var dataInput: Types.GetResourceDataInput := allNone();
    var dataOutput: Types.GetResourceDataOutput :- expect resource.GetResourceData(dataInput);
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
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysModeledError(errorInput);
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
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysMultipleErrors(errorInput);
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
    var errorOutput: Result<Types.GetExtendableResourceErrorsOutput, Types.Error>;
    errorOutput := resource.AlwaysOpaqueError(errorInput);
    CheckOpaqueError(errorOutput);
  }
}  
