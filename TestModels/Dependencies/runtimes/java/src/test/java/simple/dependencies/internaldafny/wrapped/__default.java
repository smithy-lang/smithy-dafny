// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.dependencies.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.dependencies.SimpleDependencies;
import simple.dependencies.ToNative;
import simple.dependencies.internaldafny.types.Error;
import simple.dependencies.internaldafny.types.ISimpleDependenciesClient;
import simple.dependencies.internaldafny.types.SimpleDependenciesConfig;
import simple.dependencies.wrapped.TestSimpleDependencies;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleDependenciesClient,
    Error
  > WrappedSimpleDependencies(SimpleDependenciesConfig config) {
    simple.dependencies.model.SimpleDependenciesConfig wrappedConfig =
      ToNative.SimpleDependenciesConfig(config);
    simple.dependencies.SimpleDependencies impl = SimpleDependencies
      .builder()
      .SimpleDependenciesConfig(wrappedConfig)
      .build();
    TestSimpleDependencies wrappedClient = TestSimpleDependencies
      .builder()
      .impl(impl)
      .build();
    return simple.dependencies.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
