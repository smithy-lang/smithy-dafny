// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.constraints.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.callingawssdkfromlocalservice.SimpleCallingAWSSDKFromLocalService;
import simple.callingawssdkfromlocalservice.ToNative;
import simple.callingawssdkfromlocalservice.internaldafny.types.Error;
import simple.callingawssdkfromlocalservice.internaldafny.types.ISimpleCallingAWSSDKFromLocalServiceClient;
import simple.callingawssdkfromlocalservice.internaldafny.types.SimpleCallingAWSSDKFromLocalServiceConfig;
import simple.callingawssdkfromlocalservice.wrapped.TestSimpleCallingAWSSDKFromLocalService;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleConstraintsClient,
    Error
  > WrappedSimpleCallingAWSSDKFromLocalService(
    SimpleCallingAWSSDKFromLocalServiceConfig config
  ) {
    simple.constraints.model.SimpleCallingAWSSDKFromLocalServiceConfig wrappedConfig =
      ToNative.SimpleCallingAWSSDKFromLocalServiceConfig(config);
    simple.constraints.SimpleCallingAWSSDKFromLocalService impl =
      SimpleCallingAWSSDKFromLocalService
        .builder()
        .SimpleCallingAWSSDKFromLocalServiceConfig(wrappedConfig)
        .build();
    TestSimpleCallingAWSSDKFromLocalService wrappedClient =
      TestSimpleCallingAWSSDKFromLocalService.builder().impl(impl).build();
    return simple.constraints.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
