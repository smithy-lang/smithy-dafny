// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.Set;
import software.amazon.polymorph.smithypython.localservice.ConstraintUtils;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.UnionGenerator;

/**
 * Extend Smithy-Python's UnionGenerator to write Constraint traits.
 */
public class DafnyPythonLocalServiceUnionGenerator extends UnionGenerator {

  public DafnyPythonLocalServiceUnionGenerator(
    Model model,
    SymbolProvider symbolProvider,
    PythonWriter writer,
    UnionShape shape,
    Set<Shape> recursiveShapes
  ) {
    super(model, symbolProvider, writer, shape, recursiveShapes);
  }

  @Override
  protected void writeInitMethodConstraintsChecksForMember(
    MemberShape member,
    String memberName
  ) {
    // Smithy-Python UnionGenerator hardcodes "value" as union values
    ConstraintUtils.writeInitMethodConstraintsChecksForMember(
      writer,
      model,
      member,
      "value"
    );
  }

  /**
   * Override Smithy-Python writeFromDictMethod to handle members with {@code ReferenceTrait.class}.
   * @param member
   * @param memberSymbol
   * @param target
   * @param targetSymbol
   */
  @Override
  protected void writeFromDictMethod(
    MemberShape member,
    Symbol memberSymbol,
    Shape target,
    Symbol targetSymbol
  ) {
    writer.write("@staticmethod");
    writer.openBlock(
      "def from_dict(d: Dict[str, Any]) -> $S:",
      "",
      memberSymbol.getName(),
      () -> {
        // Block below is changed from Smithy-Python.
        // Import any modules required for reference shapes to convert from_dict.
        // Import within function to avoid circular imports from top-level imports
        if (target.hasTrait(ReferenceTrait.class)) {
          writer.write(
            "from $L import $L",
            targetSymbol.getNamespace(),
            targetSymbol.getName()
          );
        }

        writer.write(
          """
          if (len(d) != 1):
              raise TypeError(f"Unions may have exactly 1 value, but found {len(d)}")
          """
        );

        // Block below is changed from Smithy-Python.
        // If shape has ReferenceTrait, write it as literal;
        // it has been imported within the context of the function.
        // Else, write as Smithy-Python default: $T.
        String targetSymbolFormat = target.hasTrait(ReferenceTrait.class)
          ? "$L"
          : "$T";
        var targetSymbolValue = target.hasTrait(ReferenceTrait.class)
          ? targetSymbol.getName()
          : targetSymbol;

        if (target.isStructureShape()) {
          writer.write(
            format("return $T(%s.from_dict(d[$S]))", targetSymbolFormat),
            memberSymbol,
            targetSymbolValue,
            member.getMemberName()
          );
        } else if (targetSymbol.getProperty("fromDict").isPresent()) {
          var targetFromDictSymbol = targetSymbol.expectProperty(
            "fromDict",
            Symbol.class
          );
          writer.write(
            "return $T($T(d[$S]))",
            memberSymbol,
            targetFromDictSymbol,
            member.getMemberName()
          );
        } else {
          writer.write(
            "return $T(d[$S])",
            memberSymbol,
            member.getMemberName()
          );
        }
      }
    );
  }

  /**
   * If a Union member has {@code ReferenceTrait.class}, handle it here.
   * Otherwise, defer to Smithy-Python writeInitMethodForMember.
   * @param member
   * @param memberSymbol
   * @param targetShape
   * @param targetSymbol
   */
  @Override
  protected void writeInitMethodForMember(
    MemberShape member,
    Symbol memberSymbol,
    Shape targetShape,
    Symbol targetSymbol
  ) {
    // Override Smithy-Python to handle shapes with ReferenceTraits
    if (targetShape.hasTrait(ReferenceTrait.class)) {
      Shape referentShape = model.expectShape(
        targetShape.expectTrait(ReferenceTrait.class).getReferentId()
      );

      // Use forward reference for reference traits to avoid circular import
      String memberType =
        symbolProvider.toSymbol(referentShape).getNamespace() +
        "." +
        symbolProvider.toSymbol(referentShape).getName();

      String formatString = format(
        "def __init__(self, value: '%s'):",
        memberType
      );
      writer.openBlock(
        formatString,
        "",
        () -> {
          writeInitMethodConstraintsChecksForMember(
            member,
            memberSymbol.getName()
          );
          writer.write("self.value = value");
        }
      );
    } else {
      super.writeInitMethodForMember(
        member,
        memberSymbol,
        targetShape,
        targetSymbol
      );
    }
  }
}
