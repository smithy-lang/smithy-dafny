package software.amazon.polymorph.smithyjava.common;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.smithy.model.shapes.StructureShape;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;

public class ModeledStructure {

    //TODO: support PositionalTrait
    public static JavaFile javaFile(String packageName, StructureShape shape, CodegenSubject subject) {
        ClassName className = ClassName.get(packageName, shape.getId().getName());
        List<FieldSpec> modelFields = BuilderSpecs.shapeToArgs(shape, subject.nativeNameResolver);
        List<FieldSpec> superFields = Collections.emptyList();
        boolean override = false;
        BuilderSpecs builderSpecs = new BuilderSpecs(className, null, modelFields, superFields);
        MethodSpec builderImplBuildMethod = BuildMethod.implBuildMethod(override, shape, subject, packageName);
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(className)
                .addModifiers(Modifier.PUBLIC)
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        override, builderSpecs.implModelConstructor(), builderImplBuildMethod)
                );
        modelFields.forEach(field -> {
            // Add fields
            spec.addField(field.type, field.name, PRIVATE, FINAL);
            // Add getter methods
            spec.addMethod(MethodSpec
                    .methodBuilder(field.name)
                    .addModifiers(Modifier.PUBLIC)
                    .returns(field.type)
                    .addStatement("return this.$L", field.name)
                    .build());
        });
        spec.addMethod(constructor(builderSpecs, modelFields))
                .addMethod(builderSpecs.toBuilderMethod(override))
                .addMethod(builderSpecs.builderMethod());

        return JavaFile.builder(packageName, spec.build())
                .skipJavaLangImports(true)
                .build();
    }

    private static MethodSpec constructor(BuilderSpecs builderSpecs, List<FieldSpec> fields) {
        MethodSpec.Builder method =  MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR);
        fields.forEach(field -> method.addStatement(
                "this.$L = $L.$L()",
                field.name, BuilderSpecs.BUILDER_VAR, field.name
        ));
        return method.build();
    }
}
