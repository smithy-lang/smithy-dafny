package software.amazon.polymorph.smithyjava.unmodeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;

import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;

/**
 * OpaqueError is a Native-Java allegory to smithy-dafny's
 * {@code datatype Error}'s {@code Opaque(obj: object)} constructor<p>
 * There is no Smithy Shape for this.<p>
 */
public class OpaqueError {
    public final static String OPAQUE_ERROR = "OpaqueError";

    /** The class name of a module's Opaque Error. */
    public static ClassName nativeClassName(String packageName) {
        return ClassName.get(packageName, OPAQUE_ERROR);
    }

    /** A JavaFile containing the OpaqueError class definition. */
    public static JavaFile javaFile(String packageName) {
        ClassName className = nativeClassName(packageName);
        ClassName superName = ClassName.get(RuntimeException.class);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, null, BuilderMemberSpec.OPAQUE_ARGS, Collections.emptyList());
        final boolean overrideSuperFalse = false;

        TypeSpec.Builder spec = TypeSpec
                .classBuilder(className)
                .addModifiers(PUBLIC)
                .superclass(superName)
                .addField(TypeName.get(Object.class), "obj", PRIVATE, FINAL)
                .addMethod(ErrorHelpers.messageFromBuilder(builderSpecs))
                .addMethods(ErrorHelpers.throwableGetters())
                .addMethod(MethodSpec
                        .methodBuilder("obj")
                        .returns(Object.class)
                        .addModifiers(PUBLIC)
                        .addStatement("return this.$L", "obj")
                        .build())
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        overrideSuperFalse,
                        builderImplConstructor(packageName),
                        builderSpecs.implBuildMethod(overrideSuperFalse))
                )
                .addMethod(constructor(builderSpecs))
                .addMethod(builderSpecs.toBuilderMethod(overrideSuperFalse))
                .addMethod(builderSpecs.builderMethod());

        return JavaFile.builder(packageName, spec.build())
                .skipJavaLangImports(true)
                .build();
    }

    /** The Class's constructor.*/
    static MethodSpec constructor(BuilderSpecs builderSpecs) {
        MethodSpec.Builder method =  MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
                .addStatement(
                        "super(messageFromBuilder($L), $L.cause())",
                        BuilderSpecs.BUILDER_VAR, BuilderSpecs.BUILDER_VAR
                )
                .addStatement("this.obj = builder.obj()");
        return method.build();
    }

    /**
     * @return Constructor that that uses {@code RuntimeException}'s getter
     * methods to initialize builder.
     */
    static MethodSpec builderImplConstructor(String packageName) {
        return MethodSpec.constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(nativeClassName(packageName), "model")
                .addStatement("this.cause = model.getCause()")
                .addStatement("this.message = model.getMessage()")
                .addStatement("this.obj = model.obj()")
                .build();
    }
}
