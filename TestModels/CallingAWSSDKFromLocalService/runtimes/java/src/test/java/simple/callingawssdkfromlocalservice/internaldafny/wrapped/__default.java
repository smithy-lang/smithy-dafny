// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.callingawssdkfromlocalservice.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.callingawssdkfromlocalservice.SimpleCallingAWSSDKFromLocalService;
import simple.callingawssdkfromlocalservice.ToNative;
import simple.callingawssdkfromlocalservice.internaldafny.types.Error;
import simple.callingawssdkfromlocalservice.internaldafny.types.ISimpleCallingAWSSDKFromLocalServiceClient;
import simple.callingawssdkfromlocalservice.internaldafny.types.SimpleCallingAWSSDKFromLocalServiceConfig;
import simple.callingawssdkfromlocalservice.wrapped.TestSimpleCallingAWSSDKFromLocalService;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleCallingAWSSDKFromLocalServiceClient,
    Error
  > WrappedSimpleCallingAWSSDKFromLocalService(SimpleCallingAWSSDKFromLocalServiceConfig config) {
    simple.callingawssdkfromlocalservice.model.SimpleCallingAWSSDKFromLocalServiceConfig wrappedConfig =
      ToNative.SimpleCallingAWSSDKFromLocalServiceConfig(config);
    simple.callingawssdkfromlocalservice.SimpleCallingAWSSDKFromLocalService impl = SimpleCallingAWSSDKFromLocalService
      .builder()
      .SimpleCallingAWSSDKFromLocalServiceConfig(wrappedConfig)
      .build();
    TestSimpleCallingAWSSDKFromLocalService wrappedClient = TestSimpleCallingAWSSDKFromLocalService
      .builder()
      .impl(impl)
      .build();
    return simple.callingawssdkfromlocalservice.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
