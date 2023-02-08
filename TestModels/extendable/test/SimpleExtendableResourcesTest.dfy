// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "./Helpers.dfy"

module SimpleExtendableResourcesTest {
  import SimpleExtendableResources
  import Types = SimpleExtendableResourcesTypes
  import opened Wrappers
  import opened TestHelpers

  method {:test} TestClient()
  {
    var client :- expect SimpleExtendableResources.SimpleExtendableResources();
    TestNoneUseExtendableResources(client);
    TestSomeUseExtendableResources(client);
  }

  method TestNoneUseExtendableResources(
    client: Types.ISimpleExtendableResourcesClient
  )
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var resource: Types.IExtendableResource := DafnyFactory();
    var dataInput: Types.GetResourceDataInput := allNone();
    var useInput: Types.UseExtendableResourcesInput := Types.UseExtendableResourcesInput(
      value := resource,
      input := dataInput
    );
    var dataOutput: Types.GetResourceDataOutput :- expect resource.GetResourceData(dataInput);
    checkNone(dataOutput);
    var useOutput: Types.UseExtendableResourcesOutput :- expect client.UseExtendableResources(useInput);
    checkNone(useOutput.output);
  }

  method TestSomeUseExtendableResources(
    client: Types.ISimpleExtendableResourcesClient
  )
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var resource: Types.IExtendableResource := DafnyFactory();
    var dataInput: Types.GetResourceDataInput := allSome();
    var useInput: Types.UseExtendableResourcesInput := Types.UseExtendableResourcesInput(
      value := resource,
      input := dataInput
    );
    var dataOutput: Types.GetResourceDataOutput :- expect resource.GetResourceData(dataInput);
    checkSome(dataOutput);
    var useOutput: Types.UseExtendableResourcesOutput :- expect client.UseExtendableResources(useInput);
    checkSome(useOutput.output);
  }
}  
