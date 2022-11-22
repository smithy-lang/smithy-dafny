package software.amazon.polymorph.smithyjava.unmodeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.BuilderSpecs;

import static software.amazon.smithy.utils.StringUtils.capitalize;

import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;

/**
 * NativeError is a concrete allegory to smithy-dafny's
 * {@code datatype Error}<p>
 * Therefore, it is un-modeled.<p>
 * NativeError allows the entries of {@code datatype Error} to extend
 * {@code RuntimeException}.<p>
 */
public class NativeError {
    public static String NATIVE_ERROR = "NativeError";
    public final static List<FieldSpec> THROWABLE_ARGS = List.of(
            FieldSpec.builder(String.class, "message").build(),
            FieldSpec.builder(Throwable.class, "cause").build()
    );

    public static ClassName className(String packageName) {
        return ClassName.get(packageName, NATIVE_ERROR);
    }

    public static JavaFile javaFile(String packageName) {
        ClassName className = className(packageName);
        ClassName superName = ClassName.get(RuntimeException.class);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, null, THROWABLE_ARGS, Collections.emptyList());
        TypeSpec spec = TypeSpec
                .classBuilder(className)
                .addModifiers(PUBLIC)
                .superclass(superName)
                .addMethod(builderSpecs.builderMethod())
                .addMethod(builderSpecs.toBuilderMethod(false))
                .addMethod(constructor(builderSpecs))
                .addMethod(messageFromBuilder(builderSpecs))
                .addType(builderSpecs.builderImpl(
                        false,
                        builderImplConstructor(packageName),
                        builderSpecs.implBuildMethod(false))
                )
                .addType(builderSpecs.builderInterface())
                .addMethods(getters())
                .build();
        return JavaFile.builder(packageName, spec)
                .skipJavaLangImports(true)
                .build();
    }

    /**
     * @return Constructor that explicitly call's {@code RuntimeException}'s
     * constructor.<p>
     * Looks for a valid message via {@code messageFromBuilder}.
     */
    static MethodSpec constructor(BuilderSpecs builderSpecs) {
        return MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
                .addStatement(
                        "super(messageFromBuilder($L), $L.cause())",
                        BuilderSpecs.BUILDER_VAR, BuilderSpecs.BUILDER_VAR
                ).build();
    }

    /**
     * @return MethodSpec that checks the message field and cause's
     * message field for a valid message.
     */
    static MethodSpec messageFromBuilder(BuilderSpecs builderSpecs) {
        return MethodSpec.methodBuilder("messageFromBuilder")
                .returns(String.class)
                .addModifiers(PRIVATE, STATIC)
                .addParameter(builderSpecs.builderInterfaceName(), BuilderSpecs.BUILDER_VAR)
                .beginControlFlow("if ($L.message() != null)", BuilderSpecs.BUILDER_VAR)
                .addStatement("return $L.message()", BuilderSpecs.BUILDER_VAR)
                .endControlFlow()
                .beginControlFlow("if ($L.cause() != null)", BuilderSpecs.BUILDER_VAR)
                .addStatement("return $L.cause().getMessage()", BuilderSpecs.BUILDER_VAR)
                .endControlFlow()
                .addStatement("return null")
                .build();
    }

    /**
     * @return Constructor that that uses {@code RuntimeException}'s getter
     * methods to initialize builder.
     */
    static MethodSpec builderImplConstructor(String packageName) {
        return MethodSpec.constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(ClassName.get(packageName, NATIVE_ERROR), "model")
                .addStatement("this.cause = model.getCause()")
                .addStatement("this.message = model.getMessage()")
                .build();
    }

    /**
     * RuntimeException's fields are retrieved by `get + capitalize-field-name`,
     * but our generated Java just uses the field name.
     */
    static Iterable<MethodSpec> getters() {
        return THROWABLE_ARGS.stream().map(field ->
                MethodSpec.methodBuilder(field.name)
                        .returns(field.type)
                        .addModifiers(PUBLIC)
                        .addStatement("return this.$L()",
                                String.format("get%s", capitalize(field.name)))
                        .build()).collect(Collectors.toList());
    }
}
