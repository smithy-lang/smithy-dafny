// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.errors.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.errors.SimpleErrors;
import simple.errors.ToNative;
import simple.errors.internaldafny.types.Error;
import simple.errors.internaldafny.types.ISimpleErrorsClient;
import simple.errors.internaldafny.types.SimpleErrorsConfig;
import simple.errors.wrapped.TestSimpleErrors;

public class __default extends _ExternBase___default {

  public static Result<ISimpleErrorsClient, Error> WrappedSimpleErrors(
    SimpleErrorsConfig config
  ) {
    simple.errors.model.SimpleErrorsConfig wrappedConfig =
      ToNative.SimpleErrorsConfig(config);
    simple.errors.SimpleErrors impl = SimpleErrors
      .builder()
      .SimpleErrorsConfig(wrappedConfig)
      .build();
    TestSimpleErrors wrappedClient = TestSimpleErrors
      .builder()
      .impl(impl)
      .build();
    return simple.errors.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
