// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleLocalServiceTest.dfy"

module WrappedTest {
  import opened SimpleLocalServiceTest
  import WrappedSimpleLocalService
  import opened Types = SimpleLocalServiceTypes
  import opened Wrappers

  method {:test} WrappedTest() {

    var client :- expect WrappedSimpleLocalService.WrappedSimpleLocalService(WrappedSimpleLocalService.WrappedDefaultSimpleLocalServiceConfig());
    var client2 :- expect WrappedSimpleLocalService.WrappedSimpleLocalService(WrappedSimpleLocalService.WrappedDefaultSimpleLocalServiceConfig());
    SimpleLocalServiceTest.TestClientDirect(client);
    SimpleLocalServiceTest.TestClientSelfReference(client, client2);
  }
}
