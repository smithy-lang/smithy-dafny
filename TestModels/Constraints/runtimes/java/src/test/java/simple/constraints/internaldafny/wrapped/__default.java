// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.constraints.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.constraints.Constraints;
import simple.constraints.ToNative;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;
import simple.constraints.internaldafny.types.SimpleConstraintsConfig;
import simple.constraints.wrapped.TestConstraints;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleConstraintsClient,
    Error
  > WrappedConstraints(SimpleConstraintsConfig config) {
    simple.constraints.model.SimpleConstraintsConfig wrappedConfig =
      ToNative.SimpleConstraintsConfig(config);
    simple.constraints.Constraints impl = Constraints
      .builder()
      .SimpleConstraintsConfig(wrappedConfig)
      .build();
    TestConstraints wrappedClient = TestConstraints
      .builder()
      .impl(impl)
      .build();
    return simple.constraints.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
