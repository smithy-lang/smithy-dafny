// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.resources.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.resources.SimpleResources;
import simple.resources.ToNative;
import simple.resources.internaldafny.types.Error;
import simple.resources.internaldafny.types.ISimpleResourcesClient;
import simple.resources.internaldafny.types.SimpleResourcesConfig;
import simple.resources.wrapped.TestSimpleResources;

public class __default extends _ExternBase___default {

  public static Result<ISimpleResourcesClient, Error> WrappedSimpleResources(
    SimpleResourcesConfig config
  ) {
    simple.resources.model.SimpleResourcesConfig wrappedConfig =
      ToNative.SimpleResourcesConfig(config);
    simple.resources.SimpleResources impl = SimpleResources
      .builder()
      .SimpleResourcesConfig(wrappedConfig)
      .build();
    TestSimpleResources wrappedClient = TestSimpleResources
      .builder()
      .impl(impl)
      .build();
    return simple.resources.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
