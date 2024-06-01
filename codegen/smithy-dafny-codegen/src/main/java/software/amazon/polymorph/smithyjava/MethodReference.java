// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.generator.Generator;

public record MethodReference(TypeName typeName, String methodName) {
  public CodeBlock asNormalReference() {
    // Special case of Identity, which should not be invoked, or
    // it will cast the input to Object.
    // Instead, do nothing!
    if (this == Generator.Constants.IDENTITY_FUNCTION) {
      return CodeBlock.builder().build();
    }
    return CodeBlock.of("$T.$L", typeName, methodName);
  }
  public CodeBlock asFunctionalReference() {
    // Special case of Identity, which cannot be functionally referenced via ::
    // but is instead functionally referenced by Function.identity()
    if (this == Generator.Constants.IDENTITY_FUNCTION) {
      return CodeBlock.of("$T.$L()", typeName, methodName);
    }
    return CodeBlock.of("$L::$L", typeName, methodName);
  }
}
