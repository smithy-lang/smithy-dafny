// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.smithydouble.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.smithydouble.SimpleDouble;
import simple.types.smithydouble.ToNative;
import simple.types.smithydouble.internaldafny.types.Error;
import simple.types.smithydouble.internaldafny.types.ISimpleTypesDoubleClient;
import simple.types.smithydouble.internaldafny.types.SimpleDoubleConfig;
import simple.types.smithydouble.wrapped.TestSimpleDouble;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesDoubleClient,
    Error
  > WrappedSimpleDouble(SimpleDoubleConfig config) {
    simple.types.smithydouble.model.SimpleDoubleConfig wrappedConfig =
      ToNative.SimpleDoubleConfig(config);
    simple.types.smithydouble.SimpleDouble impl = SimpleDouble
      .builder()
      .SimpleDoubleConfig(wrappedConfig)
      .build();
    TestSimpleDouble wrappedClient = TestSimpleDouble
      .builder()
      .impl(impl)
      .build();
    return simple.types.smithydouble.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
