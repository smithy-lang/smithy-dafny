// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.positional.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.positional.SimplePositional;
import simple.positional.ToNative;
import simple.positional.internaldafny.types.Error;
import simple.positional.internaldafny.types.ISimplePositionalClient;
import simple.positional.internaldafny.types.SimplePositionalConfig;
import simple.positional.wrapped.TestSimplePositional;

public class __default extends _ExternBase___default {

  public static Result<ISimplePositionalClient, Error> WrappedSimplePositional(
    SimplePositionalConfig config
  ) {
    simple.positional.model.SimplePositionalConfig wrappedConfig =
      ToNative.SimplePositionalConfig(config);
    simple.positional.SimplePositional impl = SimplePositional
      .builder()
      .SimplePositionalConfig(wrappedConfig)
      .build();
    TestSimplePositional wrappedClient = TestSimplePositional
      .builder()
      .impl(impl)
      .build();
    return simple.positional.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
