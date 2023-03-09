package software.amazon.smithy.dafny.codegen.runtime.java.unmodeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import software.amazon.smithy.dafny.codegen.runtime.java.BuilderSpecs;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.smithy.dafny.codegen.runtime.java.BuilderMemberSpec.OPAQUE_ARGS;
import static software.amazon.smithy.dafny.codegen.runtime.java.BuilderMemberSpec.THROWABLE_ARGS;

public class OpaqueError {
    public final static String OPAQUE_ERROR = "OpaqueError";

    public static ClassName nativeClassName(String packageName) {
        return ClassName.get(packageName, OPAQUE_ERROR);
    }

    public static JavaFile javaFile(String packageName) {
        ClassName className = nativeClassName(packageName);
        ClassName superName = NativeError.nativeClassName(packageName);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, superName, OPAQUE_ARGS, THROWABLE_ARGS);
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(className)
                .addModifiers(PUBLIC)
                .superclass(superName)
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        true,
                        builderSpecs.implModelConstructor(),
                        builderSpecs.implBuildMethod(true))
                )
                .addMethod(constructor(builderSpecs))
                .addMethod(builderSpecs.toBuilderMethod(true))
                .addMethod(builderSpecs.builderMethod());
        OPAQUE_ARGS.forEach(field -> {
            spec.addField(field.type, field.name, PRIVATE, FINAL);
            spec.addMethod(MethodSpec
                    .methodBuilder(field.name)
                    .returns(field.type)
                    .addModifiers(PUBLIC)
                    .addStatement("return this.$L", field.name)
                    .build());
        });
        return JavaFile.builder(packageName, spec.build())
                .skipJavaLangImports(true)
                .build();
    }

    static MethodSpec constructor(BuilderSpecs builderSpecs) {
        MethodSpec.Builder method =  MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
                .addStatement("super($L)", BuilderSpecs.BUILDER_VAR);
        OPAQUE_ARGS.forEach(field ->
                method.addStatement(
                        "this.$L = $L.$L()",
                        field.name, BuilderSpecs.BUILDER_VAR, field.name
                ));
        return method.build();
    }
}
