// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleLocalServiceTest.dfy"

module WrappedTest {
  import opened SimpleLocalServiceTest
  import WrappedSimpleLocalServiceService
  import opened Types = SimpleLocalServiceTypes
  import opened Wrappers

  method TestWrappedClient(config: Types.SimpleLocalServiceConfig)
  {
    var client :- expect WrappedSimpleLocalServiceService.WrappedSimpleLocalService(config);
  }

  method {:test} WrappedTest() {
    TestWrappedClient(WrappedSimpleLocalServiceService.WrappedDefaultSimpleLocalServiceConfig());
  }
}
