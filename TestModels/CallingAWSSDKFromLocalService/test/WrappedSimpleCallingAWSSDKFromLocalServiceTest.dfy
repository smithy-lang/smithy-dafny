// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleCallingAWSSDKFromLocalServiceImpl.dfy"
include "SimpleCallingAWSSDKFromLocalServiceImplTest.dfy"

module WrappedSimpleCallingAWSSDKFromLocalServiceTest {
  import opened WrappedCallingAWSSDKFromLocalServiceService
  import SimpleCallingAWSSDKFromLocalServiceImplTest
  import opened Wrappers
  import opened StandardLibrary.UInt
  method{:test} TestCallDDB() {
    var client :- expect WrappedCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallDDB(client);
  }

  method{:test} TestCallKMS() {
    var client :- expect WrappedCallingAWSSDKFromLocalServiceService.WrappedSimpleCallingAWSSDKFromLocalService();
    SimpleCallingAWSSDKFromLocalServiceImplTest.TestCallKMS(client);
  }
}