// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithypython.localservice.extensions;

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

import static java.lang.String.format;

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

  @Override
  protected void writeClassLevelImports(MemberShape member, Symbol memberSymbol, Shape targetShape, Symbol targetSymbol) {
    // Override Smithy-Python to handle shapes with ReferenceTraits
    if (targetShape.hasTrait(ReferenceTrait.class)) {
      Shape referentShape =
          model.expectShape(targetShape.expectTrait(ReferenceTrait.class).getReferentId());

      writer.writeComment("Import reference class at class level to avoid circular dependency");
      writer.write(
        "from $L import $L",
        symbolProvider.toSymbol(referentShape).getNamespace(),
        symbolProvider.toSymbol(referentShape).getName()
      );
    }
    super.writeClassLevelImports(member, memberSymbol, targetShape, targetSymbol);
  }

//  @Override
//  protected void writeInitMethodForMember(MemberShape member, Symbol memberSymbol, Shape targetShape, Symbol targetSymbol) {
//    // Override Smithy-Python to handle shapes with ReferenceTraits
//    if (targetShape.hasTrait(ReferenceTrait.class)) {
//      Shape referentShape = model.expectShape(
//        targetShape.expectTrait(ReferenceTrait.class).getReferentId()
//      );
//
//      // Use forward reference for reference traits to avoid circular import
//      String memberType = symbolProvider.toSymbol(referentShape).getNamespace() +
//        "." +
//        symbolProvider.toSymbol(referentShape).getName();
//      writer.addStdlibImport(
//        symbolProvider.toSymbol(referentShape).getNamespace()
//      );
//
//      String formatString = format("def __init__(self, value: '%s'):", memberType);
//      writer.openBlock(formatString,
//        "",
//        () -> {
//          writeInitMethodConstraintsChecksForMember(member, memberSymbol.getName());
//          writer.write("self.value = value");
//        });
//    } else {
//      super.writeInitMethodForMember(member, memberSymbol, targetShape, targetSymbol);
//    }
//  }
}
