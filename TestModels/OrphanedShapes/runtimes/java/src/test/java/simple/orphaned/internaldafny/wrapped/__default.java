// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.orphaned.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.orphaned.SimpleOrphaned;
import simple.orphaned.ToNative;
import simple.orphaned.internaldafny.types.Error;
import simple.orphaned.internaldafny.types.ISimpleOrphanedClient;
import simple.orphaned.internaldafny.types.SimpleOrphanedConfig;
import simple.orphaned.wrapped.TestSimpleOrphaned;

public class __default extends _ExternBase___default {

  public static Result<ISimpleOrphanedClient, Error> WrappedSimpleOrphaned(
    SimpleOrphanedConfig config
  ) {
    simple.orphaned.model.SimpleOrphanedConfig wrappedConfig =
      ToNative.SimpleOrphanedConfig(config);
    simple.orphaned.SimpleOrphaned impl = SimpleOrphaned
      .builder()
      .SimpleOrphanedConfig(wrappedConfig)
      .build();
    TestSimpleOrphaned wrappedClient = TestSimpleOrphaned
      .builder()
      .impl(impl)
      .build();
    return simple.orphaned.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
