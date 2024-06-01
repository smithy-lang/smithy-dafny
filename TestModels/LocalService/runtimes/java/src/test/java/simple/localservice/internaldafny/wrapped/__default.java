// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.localservice.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.localservice.SimpleLocalService;
import simple.localservice.ToDafny;
import simple.localservice.ToNative;
import simple.localservice.internaldafny.types.Error;
import simple.localservice.internaldafny.types.ISimpleLocalServiceClient;
import simple.localservice.internaldafny.types.SimpleLocalServiceConfig;
import simple.localservice.wrapped.TestSimpleLocalService;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleLocalServiceClient,
    Error
  > WrappedSimpleLocalService(SimpleLocalServiceConfig config) {
    simple.localservice.model.SimpleLocalServiceConfig wrappedConfig =
      ToNative.SimpleLocalServiceConfig(config);
    simple.localservice.SimpleLocalService impl = SimpleLocalService
      .builder()
      .SimpleLocalServiceConfig(wrappedConfig)
      .build();
    TestToNativeAndToDafnyLocalService(impl);
    TestSimpleLocalService wrappedClient = TestSimpleLocalService
      .builder()
      .impl(impl)
      .build();
    return simple.localservice.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }

  // TODO: Determine how to replace this test with Dafny Source Code
  /**
   * We have not developed the ability to call ToNative from Dafny source code at this time.
   * But we need to test this un-wrapping, so this is written in native code until we figure that out.
   */
  public static void TestToNativeAndToDafnyLocalService(
    SimpleLocalService nativeValue
  ) {
    simple.localservice.internaldafny.types.ISimpleLocalServiceClient dafnyValue =
      ToDafny.SimpleLocalService(nativeValue);
    //noinspection unused
    simple.localservice.SimpleLocalService recreateNativeValue =
      ToNative.SimpleLocalService(dafnyValue);
  }
}
