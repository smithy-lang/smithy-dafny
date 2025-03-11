// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.constructor.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.constructor.SimpleConstructor;
import simple.constructor.ToNative;
import simple.constructor.internaldafny.types.Error;
import simple.constructor.internaldafny.types.ISimpleConstructorClient;
import simple.constructor.internaldafny.types.SimpleConstructorConfig;
import simple.constructor.wrapped.TestSimpleConstructor;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleConstructorClient,
    Error
  > WrappedSimpleConstructor(SimpleConstructorConfig config) {
    simple.constructor.model.SimpleConstructorConfig wrappedConfig =
      ToNative.SimpleConstructorConfig(config);
    simple.constructor.SimpleConstructor impl = SimpleConstructor
      .builder()
      .SimpleConstructorConfig(wrappedConfig)
      .build();
    TestSimpleConstructor wrappedClient = TestSimpleConstructor
      .builder()
      .impl(impl)
      .build();
    return simple.constructor.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
