// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.types.blob.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.types.blob.SimpleBlob;
import simple.types.blob.ToNative;
import simple.types.blob.internaldafny.types.Error;
import simple.types.blob.internaldafny.types.ISimpleTypesBlobClient;
import simple.types.blob.internaldafny.types.SimpleBlobConfig;
import simple.types.blob.wrapped.TestSimpleBlob;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleTypesBlobClient,
    Error
  > WrappedSimpleBlob(SimpleBlobConfig config) {
    simple.types.blob.model.SimpleBlobConfig wrappedConfig =
      ToNative.SimpleBlobConfig(config);
    simple.types.blob.SimpleBlob impl = SimpleBlob
      .builder()
      .SimpleBlobConfig(wrappedConfig)
      .build();
    TestSimpleBlob wrappedClient = TestSimpleBlob
      .builder()
      .impl(impl)
      .build();
    return simple.types.blob.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
