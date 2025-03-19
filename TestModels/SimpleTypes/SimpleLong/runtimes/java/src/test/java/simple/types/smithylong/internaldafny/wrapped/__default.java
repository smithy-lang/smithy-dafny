// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.smithylong.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.smithylong.SimpleLong;
import simple.types.smithylong.ToNative;
import simple.types.smithylong.internaldafny.types.Error;
import simple.types.smithylong.internaldafny.types.ISimpleTypesLongClient;
import simple.types.smithylong.internaldafny.types.SimpleLongConfig;
import simple.types.smithylong.wrapped.TestSimpleLong;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesLongClient,
    Error
  > WrappedSimpleLong(SimpleLongConfig config) {
    simple.types.smithylong.model.SimpleLongConfig wrappedConfig =
      ToNative.SimpleLongConfig(config);
    simple.types.smithylong.SimpleLong impl = SimpleLong
      .builder()
      .SimpleLongConfig(wrappedConfig)
      .build();
    TestSimpleLong wrappedClient = TestSimpleLong
      .builder()
      .impl(impl)
      .build();
    return simple.types.smithylong.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
