// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "./Helpers.dfy"

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
  }

  method {:test} TestDefaultConfig()
  {
    TestClient(SimpleResources.DefaultSimpleResourcesConfig());
  }

  method {:test} TestCustomConfig()
  {
    TestClient(Types.SimpleResourcesConfig(name := "Dafny"));
  }
  
}
