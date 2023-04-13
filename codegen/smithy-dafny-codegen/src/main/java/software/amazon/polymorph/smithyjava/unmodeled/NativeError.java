package software.amazon.polymorph.smithyjava.unmodeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;

import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;

import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;

/**
 * NativeError is a concrete allegory to smithy-dafny's
 * {@code datatype Error}<p>
 * Therefore, it is un-modeled.<p>
 * NativeError allows the entries of {@code datatype Error} to extend
 * {@code RuntimeException}.<p>
 */
public class NativeError {
    public static String NATIVE_ERROR = "NativeError";

    public static ClassName nativeClassName(String packageName) {
        return ClassName.get(packageName, NATIVE_ERROR);
    }

    public static JavaFile javaFile(String packageName) {
        ClassName className = nativeClassName(packageName);
        ClassName superName = ClassName.get(RuntimeException.class);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, null, BuilderMemberSpec.THROWABLE_ARGS, Collections.emptyList());
        TypeSpec spec = TypeSpec
                .classBuilder(className)
                .addModifiers(PUBLIC)
                .superclass(superName)
                .addMethod(ErrorHelpers.messageFromBuilder(builderSpecs))
                .addMethods(ErrorHelpers.throwableGetters())
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        false,
                        builderImplConstructor(packageName),
                        builderSpecs.implBuildMethod(false))
                )
                .addMethod(constructor(builderSpecs))
                .addMethod(builderSpecs.toBuilderMethod(false))
                .addMethod(builderSpecs.builderMethod())
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

}
