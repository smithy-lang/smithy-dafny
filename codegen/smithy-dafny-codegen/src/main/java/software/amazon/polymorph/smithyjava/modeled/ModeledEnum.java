// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.modeled;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PUBLIC;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

public class ModeledEnum {

  static final String VALUE_VAR = "value";
  static final String TO_STRING_METHOD_NAME = "toString";
  static final FieldSpec ENUM_VALUE_FIELD = FieldSpec
    .builder(String.class, VALUE_VAR, PRIVATE, FINAL)
    .build();

  public static JavaFile javaFile(String packageName, Shape shape) {
    ClassName className = ClassName.get(packageName, shape.getId().getName());
    TypeSpec.Builder enumSpec = TypeSpec.enumBuilder(className);
    enumSpec.addModifiers(PUBLIC);
    EnumTrait enumTrait = shape.expectTrait(EnumTrait.class);
    for (EnumDefinition value : enumTrait.getValues()) {
      if (value.getName().isEmpty()) {
        throw new IllegalArgumentException(
          "Polymorph requires that Enum Entries have a Name and a Value. " +
          "ShapeId: %s does not for value: %s".formatted(
              shape.getId(),
              value.getValue()
            )
        );
      }
      enumSpec.addEnumConstant(value.getName().get(), enumValueTypeSpec(value));
    }
    enumSpec.addField(ENUM_VALUE_FIELD);
    enumSpec.addMethod(constructor());
    enumSpec.addMethod(toStringMethod());
    ModelUtils.getDocumentationOrJavadoc(shape).map(enumSpec::addJavadoc);
    return JavaFile
      .builder(packageName, enumSpec.build())
      .skipJavaLangImports(true)
      .build();
  }

  private static TypeSpec enumValueTypeSpec(EnumDefinition value) {
    TypeSpec.Builder enumType = TypeSpec.anonymousClassBuilder(
      "$S",
      value.getValue()
    );
    if (value.getDocumentation().isPresent()) {
      enumType.addJavadoc("$S", value.getDocumentation().get());
    }
    return enumType.build();
  }

  private static MethodSpec constructor() {
    return MethodSpec
      .constructorBuilder()
      .addModifiers(PRIVATE)
      .addParameter(ENUM_VALUE_FIELD.type, ENUM_VALUE_FIELD.name)
      .addStatement(
        "this.$L = $L",
        ENUM_VALUE_FIELD.name,
        ENUM_VALUE_FIELD.name
      )
      .build();
  }

  private static MethodSpec toStringMethod() {
    return MethodSpec
      .methodBuilder(TO_STRING_METHOD_NAME)
      .returns(String.class)
      .addModifiers(PUBLIC)
      .addStatement(
        "return $T.valueOf($L)",
        String.class,
        ENUM_VALUE_FIELD.name
      )
      .build();
  }
}
