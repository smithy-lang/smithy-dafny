// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.aggregate.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.aggregate.SimpleAggregate;
import simple.aggregate.ToNative;
import simple.aggregate.internaldafny.types.Error;
import simple.aggregate.internaldafny.types.ISimpleAggregateClient;
import simple.aggregate.internaldafny.types.SimpleAggregateConfig;
import simple.aggregate.wrapped.TestSimpleAggregate;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleAggregateClient,
    Error
  > WrappedSimpleAggregate(SimpleAggregateConfig config) {
    simple.aggregate.model.SimpleAggregateConfig wrappedConfig =
      ToNative.SimpleAggregateConfig(config);
    simple.aggregate.SimpleAggregate impl = SimpleAggregate
      .builder()
      .SimpleAggregateConfig(wrappedConfig)
      .build();
    TestSimpleAggregate wrappedClient = TestSimpleAggregate
      .builder()
      .impl(impl)
      .build();
    return simple.aggregate.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
