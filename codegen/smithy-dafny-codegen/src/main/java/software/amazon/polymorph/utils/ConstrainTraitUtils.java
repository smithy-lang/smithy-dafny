// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.utils;

import java.math.BigDecimal;
import java.util.Optional;
import java.util.stream.Stream;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.Trait;

// TODO: Support idRef, pattern, uniqueItems
public class ConstrainTraitUtils {

  public static boolean hasRequiredTrait(Shape shape) {
    return shape.hasTrait(RequiredTrait.class);
  }

  public static boolean hasRangeTrait(Shape shape) {
    return shape.hasTrait(RangeTrait.class);
  }

  public static boolean hasLengthTrait(Shape shape) {
    return shape.hasTrait(LengthTrait.class);
  }

  public static boolean hasConstraintTrait(Shape shape) {
    return (
      hasRequiredTrait(shape) || hasRangeTrait(shape) || hasLengthTrait(shape)
    );
  }

  public static class RangeTraitUtils {

    /** Return the trait's min as an accurate string representation
     * that can be written in code */
    public static String minAsShapeType(Shape shape, RangeTrait trait) {
      if (trait.getMin().isEmpty()) {
        throw new IllegalArgumentException("RangeTrait has no min.");
      }
      return asShapeType(shape, trait.getMin().get());
    }

    /** Return the trait's max as an accurate string representation
     * that can be written in code */
    public static String maxAsShapeType(Shape shape, RangeTrait trait) {
      if (trait.getMax().isEmpty()) {
        throw new IllegalArgumentException("RangeTrait has no max.");
      }
      return asShapeType(shape, trait.getMax().get());
    }

    // TODO: Only INTEGER has been tested
    public static String asShapeType(Shape shape, BigDecimal value) {
      return switch (shape.getType()) {
        case BYTE -> "%d".formatted(value.byteValue());
        case SHORT -> "%d".formatted(value.shortValue());
        case INTEGER -> "%d".formatted(value.intValue());
        case LONG -> "%d".formatted(value.longValue());
        case BIG_INTEGER -> "%d".formatted(value.toBigInteger());
        case FLOAT -> "%g".formatted(value.floatValue());
        case DOUBLE -> "%g".formatted(value.doubleValue());
        case BIG_DECIMAL -> "%g".formatted(value);
        case MEMBER -> throw new IllegalArgumentException(
          """
          RangeTrait's are not defined on MemberShapes but on their target.
          The target MUST be looked up with the model.
          See software.amazon.polymorph.smithyjava.PolymorphFieldSpec.getTargetShape.
          """
        );
        default -> throw new IllegalArgumentException(
          "RangeTrait cannot apply to shape of type `%s`".formatted(
              shape.getType()
            )
        );
      };
    }
  }

  public static class LengthTraitUtils {

    public static String min(LengthTrait trait) {
      if (trait.getMin().isEmpty()) {
        throw new IllegalArgumentException("Trait has no min.");
      }
      return "%d".formatted(trait.getMin().get());
    }

    public static String max(LengthTrait trait) {
      if (trait.getMax().isEmpty()) {
        throw new IllegalArgumentException("Trait has no max.");
      }
      return "%d".formatted(trait.getMax().get());
    }
  }
}
