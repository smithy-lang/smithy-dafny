// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package %NAMESPACE%.internaldafny.wrapped;

import Wrappers_Compile.Result;
import %NAMESPACE%.%SERVICE%;
import %NAMESPACE%.ToNative;
import %NAMESPACE%.internaldafny.types.Error;
import %NAMESPACE%.internaldafny.types.I%SERVICE%Client;
import %NAMESPACE%.internaldafny.types.%SERVICE_CONFIG%;
import %NAMESPACE%.wrapped.Test%SERVICE%;

public class __default extends _ExternBase___default {

  public static Result<I%SERVICE%Client, Error> Wrapped%SERVICE%(
    %SERVICE_CONFIG% config
  ) {
    %NAMESPACE%.model.%SERVICE_CONFIG% wrappedConfig =
      ToNative.%SERVICE_CONFIG%(config);
    %NAMESPACE%.%SERVICE% impl = %SERVICE%
      .builder()
      .%SERVICE_CONFIG%(wrappedConfig)
      .build();
    Test%SERVICE% wrappedClient = Test%SERVICE%
      .builder()
      .impl(impl)
      .build();
    return %NAMESPACE%.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
