// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "./Helpers.dfy"
include "../src/MutableResource.dfy"

module SimpleResourcesTest {
  import SimpleResources
  import Types = SimpleResourcesTypes
  import opened Wrappers
  import opened Helpers

  method TestNoneGetData(
    config: Types.SimpleResourcesConfig,
    resource: Types.ISimpleResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var input := allNone();
    var result :- expect resource.GetResourceData(input);
    checkMostNone(config.name, result);
  }

  method TestSomeGetData(
    config: Types.SimpleResourcesConfig,
    resource: Types.ISimpleResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var input := allSome();
    var output :- expect resource.GetResourceData(input);
    checkSome(config.name, output);
  }

  method TestGetResources(
    config: Types.SimpleResourcesConfig,
    client: Types.ISimpleResourcesClient
  ) returns (
      resource: Types.ISimpleResource
    )
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
    ensures resource.Modifies !! {client.History}
    ensures fresh(resource.Modifies - client.Modifies - {client.History} )
    ensures resource.ValidState() && fresh(resource)
  {
    var input := Types.GetResourcesInput(
      value := Some("Test")
    );
    var output :- expect client.GetResources(input);
    return output.output;
  }

  method TestClient(config: Types.SimpleResourcesConfig)
  {
    var client :- expect SimpleResources.SimpleResources(config);
    var resource := TestGetResources(config, client);
    TestNoneGetData(config, resource);
    TestSomeGetData(config, resource);

    var mutableResource := TestGetMutableResources(config, client);
    TestMutableNoneGetData(config, mutableResource);
    TestMutableSomeGetData(config, mutableResource);
  }

  method {:test} TestDefaultConfig()
  {
    TestClient(SimpleResources.DefaultSimpleResourcesConfig());
  }

  method {:test} TestCustomConfig()
  {
    TestClient(Types.SimpleResourcesConfig(name := "Dafny"));
  }

  // This is breaking encapsulation 
  // this is not something for public clients to do.
  // this is to access the internal state and verify that specific things are true/false.
  import MutableResource = MutableResource`ForTesting

  method TestMutableNoneGetData(
    config: Types.SimpleResourcesConfig,
    resource: Types.IMutableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var input := allMutableNone();

    expect resource is MutableResource.MutableResource;
    var test:MutableResource.MutableResource := resource;

    var before := test.MyInternalState;

    var result :- expect resource.GetMutableResourceData(input);
    checkMutableMostNone(config.name, result);

    // This sort of things SHOULD NOT be able to be proved.
    // Dafny does not have a way to say `assert something is impossible to prove;`
    // assert before != test.MyInternalState;

    // This is assuming that everything verifies
    // Given that, the Dafny in MutableResource
    // was able to prove MutableResource,
    // and the Types file was correct
    // This is a basic check to make sure
    // that this simplified separated class works.
    expect before + 1 == test.MyInternalState;
  }

  method TestMutableSomeGetData(
    config: Types.SimpleResourcesConfig,
    resource: Types.IMutableResource
  )
    requires resource.ValidState()
    modifies resource.Modifies
    ensures resource.ValidState()
  {
    var input := allMutableSome();
    var output :- expect resource.GetMutableResourceData(input);
    checkMutableSome(config.name, output);
  }

  method TestGetMutableResources(
    config: Types.SimpleResourcesConfig,
    client: Types.ISimpleResourcesClient
  ) returns (
      resource: Types.IMutableResource
    )
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
    ensures resource.Modifies !! {client.History}
    ensures fresh(resource.Modifies - client.Modifies - {client.History} )
    ensures resource.ValidState() && fresh(resource)
  {
    var input := Types.GetMutableResourcesInput(
      value := Some("Test")
    );
    var output :- expect client.GetMutableResources(input);
    return output.output;
  }

}
