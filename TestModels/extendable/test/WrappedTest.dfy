// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleExtendableResourcesTest.dfy"
include "./NativeExtendableResourceTest.dfy"
include "./Helpers.dfy"

module WrappedTest
{
  import WrappedSimpleExtendableResources
  import NativeExtendableResourceTest
  import SimpleExtendableResourcesTest
  import ExtendableResource  
  import opened Wrappers  
  import opened TestHelpers

  // Tests the Resource created purely through Dafny Source Code
  method {:test} WrappedTestClientDafnyResource()
  {
    var client :- expect WrappedSimpleExtendableResources.WrappedSimpleExtendableResources();
    var resource := SimpleExtendableResourcesTest.TestCreateExtendableResource(client);
    SimpleExtendableResourcesTest.TestNoneUseExtendableResource(client, resource);
    SimpleExtendableResourcesTest.TestSomeUseExtendableResource(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysModeledError(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysMultipleErrors(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysOpaqueError(client, resource);
  }


  // Tests the Resource created through an Extern
  method {:test} WrappedTestClientNativeResource()
  {
    var client :- expect WrappedSimpleExtendableResources.WrappedSimpleExtendableResources();
    var resource := DafnyFactory();
    assert fresh(resource.Modifies - client.Modifies - {client.History});
    SimpleExtendableResourcesTest.TestNoneUseExtendableResource(client, resource);
    SimpleExtendableResourcesTest.TestSomeUseExtendableResource(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysModeledError(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysMultipleErrors(client, resource);
    SimpleExtendableResourcesTest.TestUseAlwaysOpaqueError(client, resource);
  }
}
