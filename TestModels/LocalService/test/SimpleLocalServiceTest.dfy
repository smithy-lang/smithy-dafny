// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"

module SimpleLocalServiceTest {
  import SimpleLocalService
  import Types = SimpleLocalServiceTypes
  import opened Wrappers

  method TestClientDirect(client: Types.ISimpleLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    var ret :- expect client.HelloWorld(Types.HelloWorldInput());
    expect ret.greeting == "Hi there!";
  }

  method TestClientSelfReference(client: Types.ISimpleLocalServiceClient, client2: Types.ISimpleLocalServiceClient)
    requires client.ValidState()
    requires client2.ValidState()
    requires client.Modifies !! client2.Modifies
    modifies client.Modifies
    modifies client2.Modifies
    ensures client.ValidState()
  {
    var ret :- expect client.SelfReflection(Types.SelfReflectionInput(client := client2));
    expect ret.greeting == "I looked deep within myself, and I said 'Hi there!'";
  }

  method {:test} Test()
  {
    var client :- expect SimpleLocalService.SimpleLocalService(SimpleLocalService.DefaultSimpleLocalServiceConfig());
    var client2 :- expect SimpleLocalService.SimpleLocalService(SimpleLocalService.DefaultSimpleLocalServiceConfig());
    TestClientDirect(client);
    TestClientSelfReference(client, client2);
  }

}
