// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.union.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.union.SimpleUnion;
import simple.union.ToNative;
import simple.union.internaldafny.types.Error;
import simple.union.internaldafny.types.ISimpleUnionClient;
import simple.union.internaldafny.types.SimpleUnionConfig;
import simple.union.wrapped.TestSimpleUnion;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleUnionClient,
    Error
  > WrappedSimpleUnion(SimpleUnionConfig config) {
    simple.union.model.SimpleUnionConfig wrappedConfig =
      ToNative.SimpleUnionConfig(config);
    simple.union.SimpleUnion impl = SimpleUnion
      .builder()
      .SimpleUnionConfig(wrappedConfig)
      .build();
    TestSimpleUnion wrappedClient = TestSimpleUnion
      .builder()
      .impl(impl)
      .build();
    return simple.union.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
