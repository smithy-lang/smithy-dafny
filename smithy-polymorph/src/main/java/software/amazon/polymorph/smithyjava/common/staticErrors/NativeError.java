package software.amazon.polymorph.smithyjava.common.staticErrors;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;

import software.amazon.polymorph.smithyjava.common.BuilderSpecs;

import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;

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
                .addMethod(superBuilder(builderSpecs))
                .addMethod(messageFromBuilder(builderSpecs))
                .addType(builderSpecs.builderImpl(false, builderImplConstructor(packageName)))
                .addType(builderSpecs.builderInterface())
                .build();
        return JavaFile.builder(packageName, spec)
                .skipJavaLangImports(true)
                .build();
    }

    static MethodSpec superBuilder(BuilderSpecs builderSpecs) {
        return MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
                .addStatement(
                        "super(messageFromBuilder($L), $L.cause())",
                        BuilderSpecs.BUILDER_VAR, BuilderSpecs.BUILDER_VAR
                ).build();
    }

    static MethodSpec messageFromBuilder(BuilderSpecs builderSpecs) {
        /*
        private static String messageFromBuilder(Builder builder) {
          if (builder.message() != null) {
            return builder.message();
          }
          if (builder.cause() != null) {
            return builder.cause().getMessage();
          }
          return null;
        }*/
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

    static MethodSpec builderImplConstructor(String packageName) {
        return MethodSpec.constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(ClassName.get(packageName, NATIVE_ERROR), "model")
                .addStatement("this.cause = model.getCause()")
                .addStatement("this.message = model.getMessage()")
                .build();
    }
}
