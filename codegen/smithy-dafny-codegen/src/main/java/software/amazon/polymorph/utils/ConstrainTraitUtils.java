// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.utils;

import java.math.BigDecimal;
import java.util.Optional;
import java.util.stream.Stream;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.utils.Pair;

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

  /**
   * Utility class to generate validation expressions for all members of a structure.
   *
   * @param <V> type of validation expressions, typically {@link String} or {@link TokenTree}
   */
  public abstract static class ValidationGenerator<V> {

    protected abstract V validateRequired(MemberShape memberShape);

    protected abstract V validateRange(
      MemberShape memberShape,
      RangeTrait rangeTrait
    );

    protected abstract V validateLength(
      MemberShape memberShape,
      LengthTrait lengthTrait
    );

    /**
     * Returns a stream of constraint traits that Polymorph-generated code should enforce
     * on any code path that invokes a service or resource operation,
     * from either the given shape or the targeted shape (if the given shape is a member shape).
     */
    private Stream<? extends Trait> enforcedConstraints(
      final Model model,
      final Shape shape
    ) {
      return Stream
        .of(
          shape.getMemberTrait(model, RequiredTrait.class),
          shape.getMemberTrait(model, RangeTrait.class),
          shape.getMemberTrait(model, LengthTrait.class)
        )
        .flatMap(Optional::stream);
    }

    public Stream<V> generateValidations(
      final Model model,
      final StructureShape structureShape
    ) {
      return structureShape
        .getAllMembers()
        .values()
        .stream()
        .flatMap(memberShape ->
          enforcedConstraints(model, memberShape)
            .map(trait -> Pair.of(memberShape, trait))
        )
        .map(memberTrait -> {
          final MemberShape memberShape = memberTrait.left;
          final Trait trait = memberTrait.right;
          if (trait instanceof RequiredTrait) {
            return validateRequired(memberShape);
          } else if (trait instanceof RangeTrait rangeTrait) {
            return validateRange(memberShape, rangeTrait);
          } else if (trait instanceof LengthTrait lengthTrait) {
            return validateLength(memberShape, lengthTrait);
          }
          throw new UnsupportedOperationException(
            "Unsupported constraint trait %s on shape %s".formatted(trait)
          );
        });
    }
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
