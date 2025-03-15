// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.callingawssdkfromlocalservice.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.callingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice;
import simple.callingawssdkfromlocalservice.ToNative;
import simple.callingawssdkfromlocalservice.internaldafny.types.Error;
import simple.callingawssdkfromlocalservice.internaldafny.types.ISimpleCallingAWSSDKFromLocalServiceClient;
import simple.callingawssdkfromlocalservice.internaldafny.types.SimpleCallingawssdkfromlocalserviceConfig;
import simple.callingawssdkfromlocalservice.wrapped.TestSimpleCallingawssdkfromlocalservice;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleCallingAWSSDKFromLocalServiceClient,
    Error
  > WrappedSimpleCallingawssdkfromlocalservice(SimpleCallingawssdkfromlocalserviceConfig config) {
    simple.callingawssdkfromlocalservice.model.SimpleCallingawssdkfromlocalserviceConfig wrappedConfig =
      ToNative.SimpleCallingawssdkfromlocalserviceConfig(config);
    simple.callingawssdkfromlocalservice.SimpleCallingawssdkfromlocalservice impl = SimpleCallingawssdkfromlocalservice
      .builder()
      .SimpleCallingawssdkfromlocalserviceConfig(wrappedConfig)
      .build();
    TestSimpleCallingawssdkfromlocalservice wrappedClient = TestSimpleCallingawssdkfromlocalservice
      .builder()
      .impl(impl)
      .build();
    return simple.callingawssdkfromlocalservice.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
