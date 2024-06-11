// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package $namespace:L.internaldafny.wrapped;

import Wrappers_Compile.Result;
import $namespace:L.$service:L;
import $namespace:L.ToNative;
import $namespace:L.internaldafny.types.Error;
import $namespace:L.internaldafny.types.I$service:LClient;
import $namespace:L.internaldafny.types.$serviceConfig:L;
import $namespace:L.wrapped.Test$service:L;

public class __default extends _ExternBase___default {

  public static Result<I$service:LClient, Error> Wrapped$service:L(
    $serviceConfig:L config
  ) {
    $namespace:L.model.$serviceConfig:L wrappedConfig =
      ToNative.$serviceConfig:L(config);
    $namespace:L.$service:L impl = $service:L
      .builder()
      .$serviceConfig:L(wrappedConfig)
      .build();
    Test$service:L wrappedClient = Test$service:L
      .builder()
      .impl(impl)
      .build();
    return $namespace:L.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
