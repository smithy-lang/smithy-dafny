// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.multiplemodels.primaryproject.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.multiplemodels.primaryproject.PrimaryProject;
import simple.multiplemodels.primaryproject.ToNative;
import simple.multiplemodels.primaryproject.internaldafny.types.Error;
import simple.multiplemodels.primaryproject.internaldafny.types.IPrimaryProjectClient;
import simple.multiplemodels.primaryproject.internaldafny.types.PrimaryProjectConfig;
import simple.multiplemodels.primaryproject.wrapped.TestPrimaryProject;

public class __default extends _ExternBase___default {

  public static Result<IPrimaryProjectClient, Error> WrappedPrimaryProject(
    PrimaryProjectConfig config
  ) {
    simple.multiplemodels.primaryproject.model.PrimaryProjectConfig wrappedConfig =
      ToNative.PrimaryProjectConfig(config);
    simple.multiplemodels.primaryproject.PrimaryProject impl = PrimaryProject
      .builder()
      .PrimaryProjectConfig(wrappedConfig)
      .build();
    TestPrimaryProject wrappedClient = TestPrimaryProject
      .builder()
      .impl(impl)
      .build();
    return simple.multiplemodels.primaryproject.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
