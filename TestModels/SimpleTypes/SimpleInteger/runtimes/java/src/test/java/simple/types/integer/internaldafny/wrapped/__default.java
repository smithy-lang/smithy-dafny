// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.integer.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.integer.SimpleInteger;
import simple.types.integer.ToNative;
import simple.types.integer.internaldafny.types.Error;
import simple.types.integer.internaldafny.types.ISimpleTypesIntegerClient;
import simple.types.integer.internaldafny.types.SimpleIntegerConfig;
import simple.types.integer.wrapped.TestSimpleInteger;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesIntegerClient,
    Error
  > WrappedSimpleInteger(SimpleIntegerConfig config) {
    simple.types.integer.model.SimpleIntegerConfig wrappedConfig =
      ToNative.SimpleIntegerConfig(config);
    simple.types.integer.SimpleInteger impl = SimpleInteger
      .builder()
      .SimpleIntegerConfig(wrappedConfig)
      .build();
    TestSimpleInteger wrappedClient = TestSimpleInteger
      .builder()
      .impl(impl)
      .build();
    return simple.types.integer.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
