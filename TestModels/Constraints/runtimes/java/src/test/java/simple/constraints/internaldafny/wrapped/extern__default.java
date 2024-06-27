// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package WrappedSimpleConstraintsService;

import software.amazon.cryptography.standardlibrary.internaldafny.Wrappers.Result;
import simple.constraints.SimpleConstraints;
import simple.constraints.ToNative;
import simple.constraints.internaldafny.SimpleConstraintsTypes.Error;
import simple.constraints.internaldafny.SimpleConstraintsTypes.ISimpleConstraintsClient;
import simple.constraints.internaldafny.SimpleConstraintsTypes.SimpleConstraintsConfig;

public class extern__default extends __default {

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
    return simple.constraints.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
