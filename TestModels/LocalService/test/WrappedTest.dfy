// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleLocalServiceTest.dfy"

module WrappedTest {
  import opened SimpleLocalServiceTest
  import WrappedSimpleLocalService
  import opened Types = SimpleLocalServiceTypes
  import opened Wrappers

  method TestWrappedClient(config: Types.SimpleLocalServiceConfig)
  {
    var client :- expect WrappedSimpleLocalService.WrappedSimpleLocalService(config);
  }

  method {:test} WrappedTest() {
    TestWrappedClient(WrappedSimpleLocalService.WrappedDefaultSimpleLocalServiceConfig());
  }
}
