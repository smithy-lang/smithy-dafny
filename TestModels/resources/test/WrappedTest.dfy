// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

include "../src/WrappedIndex.dfy"
include "./SimpleResourcesTest.dfy"

module WrappedTest {
  import SimpleResourcesTest
  import WrappedSimpleResources
  import opened Types = SimpleResourcesTypes
  import opened Wrappers

  method {:test} SimpleResources() {
    print("\n\tStart Test Default Client Config: ");
    SimpleResourcesTest.TestGetResourcesAndDataHappy(
      WrappedSimpleResources.WrappedDefaultSimpleResourcesConfig()
    );
    print("\n\tEnd Test Default Client Config: PASSED");

    print("\n\tStart Test Custom Client Config: ");
    SimpleResourcesTest.TestGetResourcesAndDataHappy(
      Types.SimpleResourcesConfig(name := "Dafny")
    );
    print("\n\tEnd Test Custom Client Config: PASSED");
  }
}
