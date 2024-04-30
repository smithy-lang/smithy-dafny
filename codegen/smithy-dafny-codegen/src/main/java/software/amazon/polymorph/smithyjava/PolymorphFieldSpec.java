// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import com.squareup.javapoet.TypeName;
import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.ConstrainTraitUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;

public class PolymorphFieldSpec {

  public final BuilderMemberSpec fieldSpec;
  public final MemberShape shape;
  final JavaLibrary subject;
  public final TypeName type;
  public final String name;
  public final boolean hasConstraints;

  public PolymorphFieldSpec(MemberShape shape, JavaLibrary subject) {
    this.fieldSpec = new BuilderMemberSpec(shape, subject);
    this.shape = shape;
    this.subject = subject;
    this.name = this.fieldSpec.name;
    this.type = this.fieldSpec.type;
    this.hasConstraints = ConstrainTraitUtils.hasConstraintTrait(shape);
  }

  public static List<PolymorphFieldSpec> shapeToPolyFieldSpecs(
    Shape shape,
    JavaLibrary subject
  ) {
    return shape
      .members()
      .stream()
      .map(member -> new PolymorphFieldSpec(member, subject))
      .collect(Collectors.toList());
  }

  public boolean isRequired() {
    return this.shape.isRequired();
  }

  public Shape getTargetShape() {
    return this.subject.model.expectShape(this.shape.getTarget());
  }

  public Optional<RangeTrait> rangeTrait() {
    return this.shape.getMemberTrait(subject.model, RangeTrait.class);
  }

  public Optional<BigDecimal> rangeMin() {
    return rangeTrait().flatMap(RangeTrait::getMin);
  }

  public Optional<BigDecimal> rangeMax() {
    return rangeTrait().flatMap(RangeTrait::getMax);
  }

  public Optional<LengthTrait> lengthTrait() {
    return this.shape.getMemberTrait(subject.model, LengthTrait.class);
  }

  public Optional<Long> lengthMin() {
    return lengthTrait().flatMap(LengthTrait::getMin);
  }

  public Optional<Long> lengthMax() {
    return lengthTrait().flatMap(LengthTrait::getMax);
  }

  /** Returns the Java method for getting the length of the field's type. */
  public String getLengthMethod() {
    return Native.aggregateSizeMethod(getTargetShape().getType());
  }
}
