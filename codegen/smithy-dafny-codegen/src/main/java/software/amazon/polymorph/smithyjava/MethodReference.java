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
    // We want to use this function with `ToNative.Aggregate.GenericToMap`.
    // However, the published version uses `DafnyMap<IN_KEY, IN_VALUE> dafnyValues`.
    // This should be `DafnyMap<? extends IN_KEY, ? extends IN_VALUE> dafnyValues`
    // to correctly mathe the wildcards and pass through the concrete type.
    // Tests have been added to the conversion library,
    // along with a comment, see: smithy-dafny-conversion/src/main/java/software/amazon/smithy/dafny/conversion/ToNative.java
    // By passing a very simple lambda expression,
    // the compiler can see what is going on
    // and we do not need to coordinate an update of the conversion library.
    if (this == Generator.Constants.IDENTITY_FUNCTION) {
      //      return CodeBlock.of("$T.$L()", typeName, methodName);
      return CodeBlock.of("i -> i");
    }
    return CodeBlock.of("$L::$L", typeName, methodName);
  }
}
