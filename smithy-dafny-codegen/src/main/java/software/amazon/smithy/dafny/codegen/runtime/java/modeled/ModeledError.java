package software.amazon.smithy.dafny.codegen.runtime.java.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.List;

import javax.lang.model.element.Modifier;

import software.amazon.smithy.dafny.codegen.runtime.java.BuildMethod;
import software.amazon.smithy.dafny.codegen.runtime.java.BuilderMemberSpec;
import software.amazon.smithy.dafny.codegen.runtime.java.BuilderSpecs;
import software.amazon.smithy.dafny.codegen.runtime.java.generator.library.JavaLibrary;
import software.amazon.smithy.dafny.codegen.runtime.java.unmodeled.NativeError;
import software.amazon.smithy.model.shapes.StructureShape;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;

public class ModeledError {

    public static JavaFile javaFile(String packageName, StructureShape shape, JavaLibrary subject) {
        ClassName className = ClassName.get(packageName, shape.getId().getName());
        ClassName superName = NativeError.nativeClassName(packageName);
        List<BuilderMemberSpec> modelFields = BuilderSpecs.shapeToArgs(shape, subject);
        BuilderSpecs builderSpecs = new BuilderSpecs(
                className, superName, modelFields, BuilderMemberSpec.THROWABLE_ARGS);
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(className)
                .addModifiers(Modifier.PUBLIC)
                .superclass(superName)
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        true,
                        builderSpecs.implModelConstructor(),
                        BuildMethod.implBuildMethod(
                                true,
                                shape,
                                subject,
                                packageName
                        )));
        List<BuilderMemberSpec> localFields = builderSpecs.getLocalFields();
        localFields.forEach(field -> {
            // Add local fields
            spec.addField(field.type, field.name, PRIVATE, FINAL);
            // Add getter methods
            spec.addMethod(MethodSpec
                    .methodBuilder(field.name)
                    .addModifiers(Modifier.PUBLIC)
                    .returns(field.type)
                    .addStatement("return this.$L", field.name)
                    .build());
        });
        spec.addMethod(constructor(builderSpecs, localFields))
                .addMethod(builderSpecs.toBuilderMethod(true))
                .addMethod(builderSpecs.builderMethod());

        return JavaFile.builder(packageName, spec.build())
                .skipJavaLangImports(true)
                .build();
    }

    private static MethodSpec constructor(BuilderSpecs builderSpecs, List<BuilderMemberSpec> localFields) {
        MethodSpec.Builder method =  MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
                .addStatement("super($L)", BuilderSpecs.BUILDER_VAR);
        localFields.forEach(field -> method.addStatement(
                "this.$L = $L.$L()",
                field.name, BuilderSpecs.BUILDER_VAR, field.name
        ));
        return method.build();
    }
}
