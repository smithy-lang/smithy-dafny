package software.amazon.polymorph.smithyjava.unmodeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;

import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.BuilderMemberSpec.COLLECTION_ARGS;

public class CollectionOfErrors {
    public final static String COLLECTION_ERROR = "CollectionOfErrors";

    public static ClassName nativeClassName(String packageName) {
        return ClassName.get(packageName, COLLECTION_ERROR);
    }

    public static JavaFile javaFile(String packageName) {
        ClassName className = nativeClassName(packageName);
        ClassName superName = ClassName.get(RuntimeException.class);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, null, COLLECTION_ARGS, Collections.emptyList());
        final boolean overrideSuperFalse = false;
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(className)
                .addModifiers(PUBLIC)
                .superclass(superName)
                .addField(CollectionOfErrors.exceptionList(), "list", PRIVATE, FINAL)
                .addMethod(ErrorHelpers.messageFromBuilder(builderSpecs))
                .addMethods(ErrorHelpers.throwableGetters())
                .addMethod(MethodSpec
                        .methodBuilder("list")
                        .returns(CollectionOfErrors.exceptionList())
                        .addModifiers(PUBLIC)
                        .addStatement("return this.$L", "list")
                        .build())
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        overrideSuperFalse,
                        builderImplConstructor(packageName),
                        builderSpecs.implBuildMethod(overrideSuperFalse))
                );
        spec.addMethod(constructor(builderSpecs))
                .addMethod(builderSpecs.toBuilderMethod(overrideSuperFalse))
                .addMethod(builderSpecs.builderMethod());

        return JavaFile.builder(packageName, spec.build())
                .skipJavaLangImports(true)
                .build();
    }

    public static ParameterizedTypeName exceptionList() {
        return ParameterizedTypeName.get(
                ClassName.get(List.class),
                ClassName.get(RuntimeException.class)
        );
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
                .addStatement("this.list = builder.list()");
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
                .addStatement("this.list = model.list()")
                .build();
    }
}
