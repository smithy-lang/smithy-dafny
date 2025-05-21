// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.dafnyextern.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.dafnyextern.SimpleExtern;
import simple.dafnyextern.ToNative;
import simple.dafnyextern.internaldafny.types.Error;
import simple.dafnyextern.internaldafny.types.ISimpleExternClient;
import simple.dafnyextern.internaldafny.types.SimpleExternConfig;
import simple.dafnyextern.wrapped.TestSimpleExtern;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleExternClient,
    Error
  > WrappedSimpleExtern(SimpleExternConfig config) {
    simple.dafnyextern.model.SimpleExternConfig wrappedConfig =
      ToNative.SimpleExternConfig(config);
    simple.dafnyextern.SimpleExtern impl = SimpleExtern
      .builder()
      .SimpleExternConfig(wrappedConfig)
      .build();
    TestSimpleExtern wrappedClient = TestSimpleExtern
      .builder()
      .impl(impl)
      .build();
    return simple.dafnyextern.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
