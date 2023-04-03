// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "./Helpers.dfy"
include "./NativeResourceFactory.dfy"

module SimpleExtendableResourcesTest {
  import SimpleExtendableResources
  import ExtendableResource
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers
  import opened TestHelpers
  import opened NativeResourceFactory

  const TEST_RESOURCE_NAME: string := "Dafny-Test";
  
  // Tests the Resource created purely through Dafny Source Code
  method {:test} TestClientDafnyResource()
  {
    var client :- expect SimpleExtendableResources.SimpleExtendableResources();
    // The explict type cast is needed for the `is` test on the next line
    var resource: Types.IExtendableResource := TestCreateExtendableResource(
      client, TEST_RESOURCE_NAME
    );
    expect resource is ExtendableResource.ExtendableResource;
    // The `is` test above asserts this a "pure" Dafny resource
    TestNoneUseExtendableResource(client, resource, TEST_RESOURCE_NAME);
    TestSomeUseExtendableResource(client, resource, TEST_RESOURCE_NAME);
    TestUseAlwaysModeledError(client, resource);
    TestUseAlwaysMultipleErrors(client, resource);
    TestDafnyUseAlwaysOpaqueError(client, resource);
  }

  // Test the Resource created through an Extern
  method {:test} TestClientNativeResource()
  {
    var client :- expect SimpleExtendableResources.SimpleExtendableResources();
    // The explict type cast is needed for the `is` test on the next line
    var resource: Types.IExtendableResource := DafnyFactory();
    expect !(resource is ExtendableResource.ExtendableResource);
    // The `is` test above asserts this NOT a "pure" Dafny resource
    assert fresh(resource.Modifies - client.Modifies - {client.History});
    TestNoneUseExtendableResource(client, resource, ExtendableResource.DEFAULT_RESOURCE_NAME);
    TestSomeUseExtendableResource(client, resource, ExtendableResource.DEFAULT_RESOURCE_NAME);
    TestUseAlwaysModeledError(client, resource);
    TestUseAlwaysMultipleErrors(client, resource);
    TestUseAlwaysOpaqueError(client, resource);
  }

  method TestCreateExtendableResource(
    client: Types.ISimpleExtendableResourcesClient,
    name: string
  ) returns (
    resource: Types.IExtendableResource
  )
    requires client.ValidState() && |name| > 0
    modifies client.Modifies
    ensures client.ValidState()
    ensures resource.Modifies !! {client.History}
    ensures fresh(resource.Modifies - client.Modifies - {client.History} )
    ensures resource.ValidState() && fresh(resource)
  {
    var createInput := Types.CreateExtendableResourceInput(
      name := name
    );
    var createOutput :- expect client.CreateExtendableResource(createInput);
    resource := createOutput.resource;
  }

  method TestNoneUseExtendableResource(
    client: Types.ISimpleExtendableResourcesClient,
    resource: Types.IExtendableResource,
    name: string
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()
  {
    var dataInput := allNone();
    var useInput := Types.UseExtendableResourceInput(
      resource := resource,
      input := dataInput
    );
    var useOutput :- expect client.UseExtendableResource(useInput);
    checkNone(useOutput.output, name);
  }

  method TestSomeUseExtendableResource(
    client: Types.ISimpleExtendableResourcesClient,
    resource: Types.IExtendableResource,
    name: string
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()
  {
    var dataInput := allSome();
    var useInput := Types.UseExtendableResourceInput(
      resource := resource,
      input := dataInput
    );
    var useOutput :- expect client.UseExtendableResource(useInput);
    checkSome(useOutput.output, name);
  }

  method TestUseAlwaysModeledError(
    client: Types.ISimpleExtendableResourcesClient,
    resource: Types.IExtendableResource
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()  
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var useInput := Types.UseExtendableResourceErrorsInput(
      resource := resource,
      input := errorInput
    );
    var useOutput := client.UseExtendableResourceAlwaysModeledError(
      useInput
    );
    CheckModeledError(useOutput);  
  }

  method TestUseAlwaysMultipleErrors(
    client: Types.ISimpleExtendableResourcesClient,
    resource: Types.IExtendableResource
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()  
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var useInput := Types.UseExtendableResourceErrorsInput(
      resource := resource,
      input := errorInput
    );
    var useOutput := client.UseExtendableResourceAlwaysMultipleErrors(
      useInput
    );
    CheckMultipleErrors(useOutput);  
  }
  
  method TestUseAlwaysOpaqueError(
    client: Types.ISimpleExtendableResourcesClient,
    resource: Types.IExtendableResource
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()  
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var useInput := Types.UseExtendableResourceErrorsInput(
      resource := resource,
      input := errorInput
    );
    var useOutput := client.UseExtendableResourceAlwaysOpaqueError(
      useInput
    );
    CheckOpaqueError(useOutput);  
  }


  method TestDafnyUseAlwaysOpaqueError(
    client: Types.ISimpleExtendableResourcesClient,
    resource: ExtendableResource.ExtendableResource
  )
    requires client.ValidState() && resource.ValidState()
    requires resource.Modifies !! {client.History}
    modifies client.Modifies, resource.Modifies
    ensures client.ValidState() && resource.ValidState()  
  {
    var errorInput := Types.GetExtendableResourceErrorsInput(
      value := Option.Some("Some")
    );
    var useInput := Types.UseExtendableResourceErrorsInput(
      resource := resource,
      input := errorInput
    );
    var useOutput := client.UseExtendableResourceAlwaysOpaqueError(
      useInput
    );
    CheckDafnyOpaqueError(useOutput);  
  }
}  
