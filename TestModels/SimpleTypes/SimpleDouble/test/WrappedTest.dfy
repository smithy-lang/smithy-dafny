// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleDoubleTest.dfy"

module WrappedTest {
  import opened SimpleDoubleTest
  import opened WrappedSimpleTypesDouble
  import opened Types = SimpleTypesSmithyDoubleTypes
  import opened Wrappers

  method {:test} TestWrappedClient()
  {
    var client :- expect WrappedSimpleDouble();
    TestGetDouble(client);
  }
}
