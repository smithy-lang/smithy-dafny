// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.refinement.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.refinement.SimpleRefinement;
import simple.refinement.ToNative;
import simple.refinement.internaldafny.types.Error;
import simple.refinement.internaldafny.types.ISimpleRefinementClient;
import simple.refinement.internaldafny.types.SimpleRefinementConfig;
import simple.refinement.wrapped.TestSimpleRefinement;

public class __default extends _ExternBase___default {

  public static Result<
    ISimpleRefinementClient,
    Error
  > WrappedSimpleRefinement(SimpleRefinementConfig config) {
    simple.refinement.model.SimpleRefinementConfig wrappedConfig =
      ToNative.SimpleRefinementConfig(config);
    simple.refinement.SimpleRefinement impl = SimpleRefinement
      .builder()
      .SimpleRefinementConfig(wrappedConfig)
      .build();
    TestSimpleRefinement wrappedClient = TestSimpleRefinement
      .builder()
      .impl(impl)
      .build();
    return simple.refinement.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
