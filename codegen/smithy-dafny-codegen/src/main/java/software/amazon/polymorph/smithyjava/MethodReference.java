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
    // Special case of Identity,
    // `Function.identity()` returns `Function<Object, Object>` and it captures its type from the wildcards/generics.
    // In practice with Dafny this means it will return Function.<? extends Integer>identity().
    // This is a problem because we want to return the downcast e.g. Integer.
    // Downcasting like this is not the safest thing generally,
    // but in this case we know that only Integer or whatever type is used in Dafny.
    // If some future person can make `Function.identity()` work I will be very happy!
    // However, by passing a very simple lambda expression,
    // the compiler can see what is going on.
    if (this == Generator.Constants.IDENTITY_FUNCTION) {
      //      return CodeBlock.of("$T.$L()", typeName, methodName);
      return CodeBlock.of("i -> i");
    }
    return CodeBlock.of("$L::$L", typeName, methodName);
  }
}
