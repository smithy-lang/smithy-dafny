// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/Index.dfy"
include "./Helpers.dfy"

module SimpleResourcesTest {
  import SimpleResources
  import Types = SimpleResourcesTypes
  import opened Wrappers
  import opened Helpers

  method GetResourcesClientHappy(
    config: Types.SimpleResourcesConfig
  )
    requires |config.name| > 0
  {
    var resource: Types.ISimpleResource;
    var client: Types.ISimpleResourcesClient;
    var input: Types.GetResourcesInput;
    var output: Types.GetResourcesOutput;
    var resInput: Types.GetResourceDataInput;
    var resOutput: Types.GetResourceDataOutput;

    client :- expect SimpleResources.SimpleResources(config);
    input := Types.GetResourcesInput(
      value := Option.Some("Test")
    );
    output :- expect client.GetResources(input);
    
    resInput := allNone();
    resOutput :- expect output.output.GetResourceData(resInput);
    checkMostNone(config.name, resOutput);

    resInput := allSome();
    resOutput :- expect output.output.GetResourceData(resInput);
    checkSome(config.name, resOutput);
  }

  method {:test} GetResourcesClient()
  {
    GetResourcesClientHappy(
      SimpleResources.DefaultSimpleResourcesConfig()
    );
    GetResourcesClientHappy(
      Types.SimpleResourcesConfig(name := "Dafny")
    );
  }
  
}
