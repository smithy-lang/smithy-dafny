// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package %NAMESPACE%.internaldafny.wrapped;

import Wrappers_Compile.Result;
import %NAMESPACE%.%SERVICE%;
import %NAMESPACE%.ToNative;
import %NAMESPACE%.internaldafny.types.Error;
import %NAMESPACE%.internaldafny.types.I%SERVICE%Client;
import %NAMESPACE%.internaldafny.types%SERVICE%Config;
import %NAMESPACE%.wrapped.Test%SERVICE%;

public class __default extends _ExternBase___default {

  public static Result<I%SERVICE%Client, Error> Wrapped%SERVICE%(
    %SERVICE%Config config
  ) {
    %NAMESPACE%.model.%SERVICE%Config wrappedConfig =
      ToNative.%SERVICE%Config(config);
    %NAMESPACE%.%SERVICE% impl = %SERVICE%
      .builder()
      .%SERVICE%Config(wrappedConfig)
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
