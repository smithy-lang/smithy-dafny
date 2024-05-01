// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.multiplemodels.dependencyproject.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.multiplemodels.dependencyproject.DependencyProject;
import simple.multiplemodels.dependencyproject.ToNative;
import simple.multiplemodels.dependencyproject.internaldafny.types.DependencyProjectConfig;
import simple.multiplemodels.dependencyproject.internaldafny.types.Error;
import simple.multiplemodels.dependencyproject.internaldafny.types.IDependencyProjectClient;
import simple.multiplemodels.dependencyproject.wrapped.TestDependencyProject;

public class __default extends _ExternBase___default {

  public static Result<
    IDependencyProjectClient,
    Error
  > WrappedDependencyProject(DependencyProjectConfig config) {
    simple.multiplemodels.dependencyproject.model.DependencyProjectConfig wrappedConfig =
      ToNative.DependencyProjectConfig(config);
    simple.multiplemodels.dependencyproject.DependencyProject impl =
      DependencyProject
        .builder()
        .DependencyProjectConfig(wrappedConfig)
        .build();
    TestDependencyProject wrappedClient = TestDependencyProject
      .builder()
      .impl(impl)
      .build();
    return simple.multiplemodels.dependencyproject.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
