package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;

import software.amazon.polymorph.smithyjava.generator.Generator;

public record MethodReference(ClassName className, String methodName) {
    public CodeBlock asNormalReference() {
        // Special case of Identity, which should not be invoked, or
        // it will cast the input to Object.
        // Instead, do nothing!
        if (this == Generator.Constants.IDENTITY_FUNCTION) {
            return CodeBlock.builder().build();
        }
        return CodeBlock.of("$T.$L", className, methodName);
    }
    public CodeBlock asFunctionalReference() {
        // Special case of Identity, which cannot be functionally referenced via ::
        // but is instead functionally referenced by Function.identity()
        if (this == Generator.Constants.IDENTITY_FUNCTION) {
            return CodeBlock.of("$T.$L()", className, methodName);
        }
        return CodeBlock.of("$L::$L", className, methodName);
    }
}


