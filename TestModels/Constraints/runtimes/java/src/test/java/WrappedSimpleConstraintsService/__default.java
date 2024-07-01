// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package WrappedSimpleConstraintsService;

import software.amazon.cryptography.standardlibrary.internaldafny.Wrappers.Result;
import simple.constraints.SimpleConstraints;
import simple.constraints.ToNative;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;
import simple.constraints.internaldafny.types.SimpleConstraintsConfig;
import simple.constraints.wrapped.TestSimpleConstraints;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleConstraintsClient,
    Error
  > WrappedSimpleConstraints(SimpleConstraintsConfig config) {
    simple.constraints.model.SimpleConstraintsConfig wrappedConfig =
      ToNative.SimpleConstraintsConfig(config);
    simple.constraints.SimpleConstraints impl = SimpleConstraints
      .builder()
      .SimpleConstraintsConfig(wrappedConfig)
      .build();
    TestSimpleConstraints wrappedClient = TestSimpleConstraints
      .builder()
      .impl(impl)
      .build();
    return simple.constraints.internaldafny.SimpleConstraints.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
