// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import java.util.List;
import java.util.Objects;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.modeled.ModeledUnion;
import software.amazon.polymorph.utils.ConstrainTraitUtils;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;

public class BuildMethod {

  /**
   * Generates a build method for a BuilderImpl that respects a shapes constraint traits.
   * The code here assumes access to a Builder's normal getter methods via `this.fieldName()`.
   * <p>
   * NOTE: Our builder pattern does NOT invoke a super's build(),
   * so a sub-class will not invoke the super's trait validation.
   * This is OK, as:
   * <ul>
   *   <li> We only intend to use super/class-hierarchy for exceptions
   *   <li> This method takes in the shape only, not the super shape, so it only knows about the local fields
   *   <li> For smithy-modeled shapes, all the fields should be defined on the shape anyhow.
   * </ul>
   */
  public static MethodSpec implBuildMethod(
    boolean overrideSuper,
    Shape shape,
    JavaLibrary subject,
    String packageName
  ) {
    ClassName className = ClassName.get(packageName, shape.getId().getName());
    List<PolymorphFieldSpec> polyFieldSpecs =
      PolymorphFieldSpec.shapeToPolyFieldSpecs(shape, subject);
    MethodSpec.Builder buildMethod = MethodSpec
      .methodBuilder("build")
      .addModifiers(Modifier.PUBLIC)
      .returns(className);
    if (overrideSuper) {
      buildMethod.addAnnotation(Override.class);
    }

    polyFieldSpecs.forEach(polyField -> {
      // Required Trait
      if (polyField.isRequired()) {
        buildMethod.addCode(requiredCheck(polyField.fieldSpec));
      }

      // Range Trait
      RangeTrait rangeTrait = polyField.rangeTrait().isPresent()
        ? polyField.rangeTrait().get()
        : null;
      if (rangeTrait != null && polyField.rangeMin().isPresent()) {
        buildMethod.addCode(rangeMinCheck(polyField, rangeTrait));
      }
      if (rangeTrait != null && polyField.rangeMax().isPresent()) {
        buildMethod.addCode(rangeMaxCheck(polyField, rangeTrait));
      }

      // Length Trait
      LengthTrait lengthTrait = polyField.lengthTrait().isPresent()
        ? polyField.lengthTrait().get()
        : null;
      if (lengthTrait != null && polyField.lengthMin().isPresent()) {
        buildMethod.addCode(lengthMinCheck(polyField, lengthTrait));
      }
      if (lengthTrait != null && polyField.lengthMax().isPresent()) {
        buildMethod.addCode(lengthMaxCheck(polyField, lengthTrait));
      }
    });

    // Union check
    if (shape.isUnionShape()) {
      buildMethod.addCode(unionCheck(shape.getId().getName()));
    }

    buildMethod.addStatement("return new $T(this)", className);
    return buildMethod.build();
  }

  static CodeBlock fieldNonNull(BuilderMemberSpec field) {
    if (field.type.isPrimitive()) {
      return CodeBlock.of("this.$L", isSetFieldName(field));
    }
    return CodeBlock.of("$T.nonNull(this.$L())", Objects.class, field.name);
  }

  static String isSetFieldName(BuilderMemberSpec field) {
    return "_%sSet".formatted(field.name);
  }

  public static CodeBlock requiredCheck(BuilderMemberSpec field) {
    CodeBlock.Builder check = CodeBlock.builder();
    if (field.type.isPrimitive()) {
      check.beginControlFlow("if (!this.$L)", isSetFieldName(field));
    } else {
      check.beginControlFlow(
        "if ($T.isNull(this.$L())) ",
        Objects.class,
        field.name
      );
    }
    return check
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "Missing value for required field `%s`".formatted(field.name)
      )
      .endControlFlow()
      .build();
  }

  static CodeBlock rangeMinCheck(
    PolymorphFieldSpec polyField,
    RangeTrait trait
  ) {
    String min = ConstrainTraitUtils.RangeTraitUtils.minAsShapeType(
      polyField.getTargetShape(),
      trait
    );
    return CodeBlock
      .builder()
      .beginControlFlow(
        "if ($L && this.$L() < $L)",
        fieldNonNull(polyField.fieldSpec),
        polyField.name,
        min
      )
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "`%s` must be greater than or equal to %s".formatted(
            polyField.name,
            min
          )
      )
      .endControlFlow()
      .build();
  }

  static CodeBlock rangeMaxCheck(
    PolymorphFieldSpec polyField,
    RangeTrait trait
  ) {
    String max = ConstrainTraitUtils.RangeTraitUtils.maxAsShapeType(
      polyField.getTargetShape(),
      trait
    );
    return CodeBlock
      .builder()
      .beginControlFlow(
        "if ($L && this.$L() > $L)",
        fieldNonNull(polyField.fieldSpec),
        polyField.name,
        max
      )
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "`%s` must be less than or equal to %s.".formatted(polyField.name, max)
      )
      .endControlFlow()
      .build();
  }

  static CodeBlock lengthMinCheck(
    PolymorphFieldSpec polyField,
    LengthTrait trait
  ) {
    String min = ConstrainTraitUtils.LengthTraitUtils.min(trait);
    return CodeBlock
      .builder()
      .beginControlFlow(
        "if ($L && this.$L().$L < $L)",
        fieldNonNull(polyField.fieldSpec),
        polyField.name,
        polyField.getLengthMethod(),
        min
      )
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "The size of `%s` must be greater than or equal to %s".formatted(
            polyField.name,
            min
          )
      )
      .endControlFlow()
      .build();
  }

  static CodeBlock lengthMaxCheck(
    PolymorphFieldSpec polyField,
    LengthTrait trait
  ) {
    String max = ConstrainTraitUtils.LengthTraitUtils.max(trait);
    return CodeBlock
      .builder()
      .beginControlFlow(
        "if ($L && this.$L().$L > $L)",
        fieldNonNull(polyField.fieldSpec),
        polyField.name,
        polyField.getLengthMethod(),
        max
      )
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "The size of `%s` must be less than or equal to %s".formatted(
            polyField.name,
            max
          )
      )
      .endControlFlow()
      .build();
  }

  static CodeBlock unionCheck(String className) {
    return CodeBlock
      .builder()
      .beginControlFlow("if (!$L())", ModeledUnion.UNION_VALIDATE_METHOD_NAME)
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "`%s` is a Union. A Union MUST have one and only one value set.".formatted(
            className
          )
      )
      .endControlFlow()
      .build();
  }
}
