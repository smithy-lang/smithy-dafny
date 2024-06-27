// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.modeled;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import javax.annotation.Nonnull;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.BuildMethod;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.Shape;

public class ModeledStructure {

  public static JavaFile javaFile(
    String packageName,
    Shape shape,
    JavaLibrary subject
  ) {
    if (!(shape.isUnionShape() || shape.isStructureShape())) {
      throw new IllegalArgumentException(
        "ModeledStructure should only be called for Structures or Unions. ShapeId: %s".formatted(
            shape.getId()
          )
      );
    }
    ClassName className = ClassName.get(packageName, shape.getId().getName());
    List<BuilderMemberSpec> modelFields = BuilderSpecs.shapeToArgs(
      shape,
      subject
    );
    List<BuilderMemberSpec> superFields = Collections.emptyList();
    boolean override = false;
    BuilderSpecs builderSpecs = new BuilderSpecs(
      className,
      null,
      modelFields,
      superFields
    );
    MethodSpec builderImplBuildMethod = BuildMethod.implBuildMethod(
      override,
      shape,
      subject,
      packageName
    );
    TypeSpec builderInterface = builderSpecs.builderInterface();
    TypeSpec builderImpl = builderSpecs.builderImpl(
      override,
      builderSpecs.implModelConstructor(),
      builderImplBuildMethod
    );
    // Unions are nearly identical to Structures,
    // except they have an additional constraint.
    if (shape.isUnionShape()) {
      // The shape is a union, "asUnionShape" will return a value
      //noinspection OptionalGetWithoutIsPresent
      builderImpl =
        builderImpl
          .toBuilder()
          .addMethod(ModeledUnion.unionValidate(shape.asUnionShape().get()))
          .build();
    }
    TypeSpec.Builder spec = TypeSpec
      .classBuilder(className)
      .addModifiers(Modifier.PUBLIC)
      .addType(builderInterface)
      .addType(builderImpl);
    ModelUtils.getDocumentationOrJavadoc(shape).map(spec::addJavadoc);
    modelFields.forEach(field -> {
      // Add fields
      spec.addField(field.toFieldSpec(PRIVATE, FINAL));
      // Add getter methods
      spec.addMethod(getterMethod(field));
    });
    spec
      .addMethod(constructor(builderSpecs, modelFields))
      .addMethod(builderSpecs.toBuilderMethod(override))
      .addMethod(builderSpecs.builderMethod());
    return JavaFile
      .builder(packageName, spec.build())
      .skipJavaLangImports(true)
      .build();
  }

  @Nonnull
  public static MethodSpec getterMethod(BuilderMemberSpec field) {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(field.name)
      .addModifiers(Modifier.PUBLIC)
      .returns(field.type)
      .addStatement("return this.$L", field.name);
    if (Objects.nonNull(field.javaDoc)) {
      method.addJavadoc("@return $L", field.javaDoc);
    }
    return method.build();
  }

  private static MethodSpec constructor(
    BuilderSpecs builderSpecs,
    List<BuilderMemberSpec> fields
  ) {
    MethodSpec.Builder method = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR);
    fields.forEach(field ->
      method.addStatement(
        "this.$L = $L.$L()",
        field.name,
        BuilderSpecs.BUILDER_VAR,
        field.name
      )
    );
    return method.build();
  }
}
