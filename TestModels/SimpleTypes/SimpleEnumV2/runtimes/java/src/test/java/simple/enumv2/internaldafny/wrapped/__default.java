// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.enumv2.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.enumv2.SimpleEnumV2;
import simple.types.enumv2.ToNative;
import simple.types.enumv2.internaldafny.types.Error;
import simple.types.enumv2.internaldafny.types.ISimpleTypesEnumV2Client;
import simple.types.enumv2.internaldafny.types.SimpleEnumV2Config;
import simple.types.enumv2.wrapped.TestSimpleEnumV2;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesEnumV2Client,
    Error
  > WrappedSimpleEnumV2(SimpleEnumV2Config config) {
    simple.types.enumv2.model.SimpleEnumV2Config wrappedConfig =
      ToNative.SimpleEnumV2Config(config);
    simple.types.enumv2.SimpleEnumV2 impl = SimpleEnumV2
      .builder()
      .SimpleEnumV2Config(wrappedConfig)
      .build();
    TestSimpleEnumV2 wrappedClient = TestSimpleEnumV2
      .builder()
      .impl(impl)
      .build();
    return simple.types.enumv2.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
