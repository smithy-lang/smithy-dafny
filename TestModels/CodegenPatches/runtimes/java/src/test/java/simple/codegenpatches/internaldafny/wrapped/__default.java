// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.codegenpatches.internaldafny.wrapped;

import Wrappers_Compile.Result;
import simple.codegenpatches.CodegenPatches;
import simple.codegenpatches.ToNative;
import simple.codegenpatches.internaldafny.types.CodegenPatchesConfig;
import simple.codegenpatches.internaldafny.types.Error;
import simple.codegenpatches.internaldafny.types.ICodegenPatchesClient;
import simple.codegenpatches.wrapped.TestCodegenPatches;

public class __default extends _ExternBase___default {

  public static Result<ICodegenPatchesClient, Error> WrappedCodegenPatches(
    CodegenPatchesConfig config
  ) {
    simple.codegenpatches.model.CodegenPatchesConfig wrappedConfig =
      ToNative.CodegenPatchesConfig(config);
    simple.codegenpatches.CodegenPatches impl = CodegenPatches
      .builder()
      .CodegenPatchesConfig(wrappedConfig)
      .build();
    TestCodegenPatches wrappedClient = TestCodegenPatches
      .builder()
      .impl(impl)
      .build();
    return simple.codegenpatches.internaldafny.__default.CreateSuccessOfClient(
      wrappedClient
    );
  }
}
