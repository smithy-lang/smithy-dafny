// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.smithystring.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.smithystring.SimpleString;
import simple.types.smithystring.ToNative;
import simple.types.smithystring.internaldafny.types.Error;
import simple.types.smithystring.internaldafny.types.ISimpleTypesStringClient;
import simple.types.smithystring.internaldafny.types.SimpleStringConfig;
import simple.types.smithystring.wrapped.TestSimpleString;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesStringClient,
    Error
  > WrappedSimpleString(SimpleStringConfig config) {
    simple.types.smithystring.model.SimpleStringConfig wrappedConfig =
      ToNative.SimpleStringConfig(config);
    simple.types.smithystring.SimpleString impl = SimpleString
      .builder()
      .SimpleStringConfig(wrappedConfig)
      .build();
    TestSimpleString wrappedClient = TestSimpleString
      .builder()
      .impl(impl)
      .build();
    return simple.types.smithystring.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
