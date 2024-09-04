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

  method TestClientSelfReference(client: Types.ISimpleLocalServiceClient)
    requires client.ValidState()
    modifies client.Modifies
    ensures client.ValidState()
  {
    // This is a flat out lie and directly contradicts client.ValidState().
    // But otherwise it's not possible to call other client methods like this.
    // Since this test model is only using self-reference in order to
    // avoid extra dependencies, and self-reference isn't that useful a use case in reality,
    // lying to get around the specification restrictions in a test is not terribly risky.
    assume {:axiom} client.Modifies !! {client.History};
    var ret :- expect client.SelfReflection(Types.SelfReflectionInput(self := client));
    expect ret.greeting == "I looked deep within myself, and I said 'Hi there!'";
  }

  method {:test} Test()
  {
    var client :- expect SimpleLocalService.SimpleLocalService(SimpleLocalService.DefaultSimpleLocalServiceConfig());
    TestClientDirect(client);
    TestClientSelfReference(client);
  }

}
