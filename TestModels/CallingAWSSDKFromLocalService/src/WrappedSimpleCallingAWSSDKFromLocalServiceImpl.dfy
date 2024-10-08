// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypesWrapped.dfy"

module {:extern "simple.callingawssdkfromlocalservice.internaldafny.wrapped"} WrappedSimpleCallingAWSSDKFromLocalServiceService refines WrappedAbstractSimpleCallingawssdkfromlocalserviceService {
  import WrappedService = SimpleCallingAWSSDKFromLocalService
  function method WrappedDefaultSimpleCallingAWSSDKFromLocalServiceConfig(): SimpleCallingAWSSDKFromLocalServiceConfig {
    SimpleCallingAWSSDKFromLocalServiceConfig
  }
}
