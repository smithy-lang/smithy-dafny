// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.smithyenum.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.smithyenum.SimpleEnum;
import simple.types.smithyenum.ToNative;
import simple.types.smithyenum.internaldafny.types.Error;
import simple.types.smithyenum.internaldafny.types.ISimpleTypesEnumClient;
import simple.types.smithyenum.internaldafny.types.SimpleEnumConfig;
import simple.types.smithyenum.wrapped.TestSimpleEnum;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesEnumClient,
    Error
  > WrappedSimpleEnum(SimpleEnumConfig config) {
    simple.types.smithyenum.model.SimpleEnumConfig wrappedConfig =
      ToNative.SimpleEnumConfig(config);
    simple.types.smithyenum.SimpleEnum impl = SimpleEnum
      .builder()
      .SimpleEnumConfig(wrappedConfig)
      .build();
    TestSimpleEnum wrappedClient = TestSimpleEnum
      .builder()
      .impl(impl)
      .build();
    return simple.types.smithyenum.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
