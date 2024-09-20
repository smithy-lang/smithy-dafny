// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithypython.localservice;

import software.amazon.polymorph.utils.ConstrainTraitUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.python.codegen.PythonWriter;

public class ConstraintUtils {

  public static void writeInitMethodConstraintsChecksForMember(
    PythonWriter writer,
    Model model,
    MemberShape member,
    String memberName
  ) {
    // RangeTrait
    Shape targetShape = model.expectShape(member.getTarget());
    if (targetShape.hasTrait(RangeTrait.class)) {
      RangeTrait rangeTrait = targetShape.getTrait(RangeTrait.class).get();
      if (rangeTrait.getMin().isPresent()) {
        writeRangeTraitMinCheckForMember(
          writer,
          model,
          member,
          memberName,
          rangeTrait
        );
      }
      if (rangeTrait.getMax().isPresent()) {
        writeRangeTraitMaxCheckForMember(
          writer,
          model,
          member,
          memberName,
          rangeTrait
        );
      }
    }

    // LengthTrait
    if (targetShape.hasTrait(LengthTrait.class)) {
      LengthTrait lengthTrait = targetShape.getTrait(LengthTrait.class).get();
      if (lengthTrait.getMin().isPresent()) {
        writeLengthTraitMinCheckForMember(writer, memberName, lengthTrait);
      }
      if (lengthTrait.getMax().isPresent()) {
        writeLengthTraitMaxCheckForMember(writer, memberName, lengthTrait);
      }
    }
  }

  /**
   * Write validation for {@link LengthTrait} min value. Called from __init__.
   *
   * @param memberName
   * @param lengthTrait
   */
  protected static void writeLengthTraitMinCheckForMember(
    PythonWriter writer,
    String memberName,
    LengthTrait lengthTrait
  ) {
    String min = ConstrainTraitUtils.LengthTraitUtils.min(lengthTrait);
    writer.openBlock(
      "if ($1L is not None) and (len($1L) < $2L):",
      "",
      memberName,
      min,
      () -> {
        writer.write(
          """
          raise ValueError("The size of $1L must be greater than or equal to $2L")
          """,
          memberName,
          min
        );
      }
    );
  }

  /**
   * Write validation for {@link LengthTrait} max value. Called from __init__.
   *
   * @param memberName
   * @param lengthTrait
   */
  protected static void writeLengthTraitMaxCheckForMember(
    PythonWriter writer,
    String memberName,
    LengthTrait lengthTrait
  ) {
    String max = ConstrainTraitUtils.LengthTraitUtils.max(lengthTrait);
    writer.openBlock(
      "if ($1L is not None) and (len($1L) > $2L):",
      "",
      memberName,
      max,
      () -> {
        writer.write(
          """
          raise ValueError("The size of $1L must be less than or equal to $2L")
          """,
          memberName,
          max
        );
      }
    );
  }

  /**
   * Write validation for {@link RangeTrait} min value. Called from __init__.
   *
   * @param member
   * @param memberName
   * @param rangeTrait
   */
  protected static void writeRangeTraitMinCheckForMember(
    PythonWriter writer,
    Model model,
    MemberShape member,
    String memberName,
    RangeTrait rangeTrait
  ) {
    String min = ConstrainTraitUtils.RangeTraitUtils.minAsShapeType(
      model.expectShape(member.getTarget()),
      rangeTrait
    );
    writer.openBlock(
      "if ($1L is not None) and ($1L < $2L):",
      "",
      memberName,
      min,
      () -> {
        writer.write(
          """
          raise ValueError("$1L must be greater than or equal to $2L")
          """,
          memberName,
          min
        );
      }
    );
  }

  /**
   * Write validation for {@link RangeTrait} max value. Called from __init__.
   *
   * @param member
   * @param memberName
   * @param rangeTrait
   */
  protected static void writeRangeTraitMaxCheckForMember(
    PythonWriter writer,
    Model model,
    MemberShape member,
    String memberName,
    RangeTrait rangeTrait
  ) {
    String max = ConstrainTraitUtils.RangeTraitUtils.maxAsShapeType(
      model.expectShape(member.getTarget()),
      rangeTrait
    );
    writer.openBlock(
      "if ($1L is not None) and ($1L > $2L):",
      "",
      memberName,
      max,
      () -> {
        writer.write(
          """
          raise ValueError("$1L must be less than or equal to $2L")
          """,
          memberName,
          max
        );
      }
    );
  }
}
