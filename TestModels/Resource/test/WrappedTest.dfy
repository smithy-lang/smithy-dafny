// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleResourcesTest.dfy"

module WrappedTest {
  import opened SimpleResourcesTest
  import WrappedSimpleResources
  import opened Types = SimpleResourcesTypes
  import opened Wrappers

  method TestWrappedClient(config: Types.SimpleResourcesConfig)
  {
    var client :- expect WrappedSimpleResources.WrappedSimpleResources(config);
    var resource := TestGetResources(config, client);
    TestNoneGetData(config, resource);
    TestSomeGetData(config, resource);
  }
  
  method {:test} WrappedTestDefaultConfig() {
    TestWrappedClient(WrappedSimpleResources.WrappedDefaultSimpleResourcesConfig());
  }

  method {:test} WrappedTestCustomConfig() {
    TestWrappedClient(Types.SimpleResourcesConfig(name := "Dafny"));
  }
}
