// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.streaming.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.streaming.SimpleStreaming;
import simple.streaming.ToNative;
import simple.streaming.internaldafny.types.Error;
import simple.streaming.internaldafny.types.ISimpleStreamingClient;
import simple.streaming.internaldafny.types.SimpleStreamingConfig;
import simple.streaming.wrapped.TestSimpleStreaming;

public class __default extends _ExternBase___default {

  public static Result<ISimpleStreamingClient, Error> WrappedSimpleStreaming(
    SimpleStreamingConfig config
  ) {
    simple.streaming.model.SimpleStreamingConfig wrappedConfig =
      ToNative.SimpleStreamingConfig(config);
    simple.streaming.SimpleStreaming impl = SimpleStreaming
      .builder()
      .SimpleStreamingConfig(wrappedConfig)
      .build();
    TestSimpleStreaming wrappedClient = TestSimpleStreaming
      .builder()
      .impl(impl)
      .build();
    return simple.streaming.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
