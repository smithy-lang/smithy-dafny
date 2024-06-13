package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.Set;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ConstrainTraitUtils;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.NullableIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.SensitiveTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.StructureGenerator;

/**
 * Override Smithy-Python's StructureGenerator:
 * - Do not render StructureShapes with {@link PositionalTrait}s
 * - Support errors from other namespaces
 * - Support {@link ReferenceTrait}s (forward references, other namespaces)
 * - Support Smithy constraints in constructors ({@link RangeTrait}, {@link LengthTrait})
 */
public class DafnyPythonLocalServiceStructureGenerator extends StructureGenerator {

  public DafnyPythonLocalServiceStructureGenerator(
      Model model,
      PythonSettings settings,
      SymbolProvider symbolProvider,
      PythonWriter writer,
      StructureShape shape,
      Set<Shape> recursiveShapes) {
    super(model, settings, symbolProvider, writer, shape, recursiveShapes);
  }

  @Override
  public void run() {
    if (shape.hasTrait(PositionalTrait.class)) {
      // Do not need to render shapes with positional trait, their linked shapes are rendered
      return;
    }
    if (!shape.hasTrait(ErrorTrait.class)) {
      renderStructure();
    } else {
      renderError();
    }
  }

  /**
   * Override Smithy-Python renderError to use the correct namespace via
   * getPythonModuleSmithygeneratedPathForSmithyNamespace.
   */
  @Override
  protected void renderError() {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    writer.addStdlibImport("typing", "Literal");
    var code = shape.getId().getName();
    var symbol = symbolProvider.toSymbol(shape);
    var apiError =
        Symbol.builder()
            .name("ApiError")
            .namespace(
                format(
                    "%s.errors",
                    SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                        settings.getService().getNamespace(), settings)),
                ".")
            .definitionFile(
                format(
                    "./%s/errors.py",
                    SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                        settings.getService().getNamespace())))
            .build();
    writer.openBlock(
        "class $L($T[Literal[$S]]):",
        "",
        symbol.getName(),
        apiError,
        code,
        () -> {
          writer.write("code: Literal[$1S] = $1S", code);
          writer.write("message: str");
          writeProperties(true);
          writeInit(true);
          writeAsDict(true);
          writeFromDict(true);
          writeRepr(true);
          writeEq(true);
        });
    writer.write("");
  }

    /**
     * Override Smithy-Python to not unambiguously write a `message`
     * attribute on errors;
     * Smithy-Dafny defines this attribute on its errors,
     * so Smithy-Python behavior is changed to not write `message` multiple times
     * @param isError
     */
  @Override
  protected void writeReprMembers(boolean isError) {
    var iter = shape.members().iterator();
    while (iter.hasNext()) {
      var member = iter.next();
      var memberName = symbolProvider.toMemberName(member);
      var trailingComma = iter.hasNext() ? ", " : "";
      if (member.hasTrait(SensitiveTrait.class)) {
        // Sensitive members must not be printed
        // see: https://smithy.io/2.0/spec/documentation-traits.html#smithy-api-sensitive-trait
        writer.write(
            """
                    if self.$1L is not None:
                        result += f"$1L=...$2L"
                    """,
            memberName,
            trailingComma);
      } else {
        writer.write(
            """
                    if self.$1L is not None:
                        result += f"$1L={repr(self.$1L)}$2L"
                    """,
            memberName,
            trailingComma);
      }
    }
  }

  /**
   * Override Smithy-Python writePropertyForMember to handle importing reference modules to avoid
   * circular imports. If the {@param memberShape} is not a reference shape or a list of reference
   * shapes, this defers to Smithy-Python's implementation. Maps containing reference shapes not
   * supported yet. (Unused in MPL.)
   *
   * @param isError
   * @param memberShape
   */
  @Override
  protected void writePropertyForMember(boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());
    String memberName = symbolProvider.toMemberName(memberShape);

    if (target.isListShape()
        && model
            .expectShape(target.asListShape().get().getMember().getTarget())
            .hasTrait(ReferenceTrait.class)) {
      Shape listMemberShape = model.expectShape(target.asListShape().get().getMember().getTarget());
      Shape referentShape =
          model.expectShape(listMemberShape.expectTrait(ReferenceTrait.class).getReferentId());
      Symbol targetSymbol = symbolProvider.toSymbol(referentShape);

      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: list['$L']";
      writer.write(
          formatString, memberName, targetSymbol.getNamespace() + "." + targetSymbol.getName());
      return;
    }

    // We currently don't have any map shapes that have values with reference traits;
    // once we do, this needs to be filled in
    if (target.isMapShape()
        && model
            .expectShape(target.asMapShape().get().getValue().getTarget())
            .hasTrait(ReferenceTrait.class)) {
      throw new IllegalArgumentException(
          "Map shapes containing references currently unsupported: " + target);
    }

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape =
          model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());

      NullableIndex index = NullableIndex.of(model);

      if (index.isMemberNullable(memberShape)) {
        writer.addStdlibImport("typing", "Optional");
        // Use forward reference for reference traits to avoid circular import
        String formatString = "$L: Optional['$L']";
        writer.write(
            formatString,
            memberName,
            symbolProvider.toSymbol(referentShape).getNamespace()
                + "."
                + symbolProvider.toSymbol(referentShape).getName());
        writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
      } else {
        // Use forward reference for reference traits to avoid circular import,
        String formatString = "$L: '$L'";
        writer.write(
            formatString,
            memberName,
            symbolProvider.toSymbol(referentShape).getNamespace()
                + "."
                + symbolProvider.toSymbol(referentShape).getName());
        writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
      }
    } else {
      super.writePropertyForMember(isError, memberShape);
    }
  }

  /**
   * Override Smithy-Python writeInitMethodParameterForRequiredMember to handle importing reference
   * modules to avoid circular imports. If the {@param memberShape} is not a reference shape or a
   * list of reference shapes, this defers to Smithy-Python's implementation. Maps containing
   * reference shapes not supported yet. (Unused in MPL.)
   *
   * @param isError
   * @param memberShape
   */
  @Override
  protected void writeInitMethodParameterForRequiredMember(
      boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());
    String memberName = symbolProvider.toMemberName(memberShape);

    if (target.isListShape()
        && model
            .expectShape(target.asListShape().get().getMember().getTarget())
            .hasTrait(ReferenceTrait.class)) {
      Shape listMemberShape = model.expectShape(target.asListShape().get().getMember().getTarget());
      Shape referentShape =
          model.expectShape(listMemberShape.expectTrait(ReferenceTrait.class).getReferentId());
      Symbol targetSymbol = symbolProvider.toSymbol(referentShape);

      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: list['$L'],";
      writer.write(
          formatString, memberName, targetSymbol.getNamespace() + "." + targetSymbol.getName());
      return;
    }

    // We currently don't have any map shapes that have values with reference traits;
    // once we do, this needs to be filled in
    if (target.isMapShape()
        && model
            .expectShape(target.asMapShape().get().getValue().getTarget())
            .hasTrait(ReferenceTrait.class)) {
      throw new IllegalArgumentException(
          "Map shapes containing references currently unsupported: " + target);
    }

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape =
          model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: '$L',";
      writer.write(
          formatString,
          memberName,
          symbolProvider.toSymbol(referentShape).getNamespace()
              + "."
              + symbolProvider.toSymbol(referentShape).getName());
      writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
    } else {
      super.writeInitMethodParameterForRequiredMember(isError, memberShape);
    }
  }

  /**
   * Override Smithy-Python writeInitMethodParameterForOptionalMember to handle importing reference
   * modules to avoid circular imports. If the {@param memberShape} is not a reference shape, this
   * defers to Smithy-Python's implementation.
   *
   * @param isError
   * @param memberShape
   */
  @Override
  protected void writeInitMethodParameterForOptionalMember(
      boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape =
          model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      String memberName = symbolProvider.toMemberName(memberShape);

      writer.addStdlibImport("typing", "Optional");
      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: Optional['$L'] = None,";
      writer.write(
          formatString,
          memberName,
          symbolProvider.toSymbol(referentShape).getNamespace()
              + "."
              + symbolProvider.toSymbol(referentShape).getName());
      writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
    } else {
      super.writeInitMethodParameterForOptionalMember(isError, memberShape);
    }
  }

  /**
   * Override Smithy-Python writeFromDict to handle importing reference modules to avoid circular
   * imports. Most of this is lifted directly from Smithy-Python; the changed component is
   * highlighted.
   *
   * @param isError
   */
  protected void writeFromDict(boolean isError) {
    writer.write("@staticmethod");
    var shapeName = symbolProvider.toSymbol(shape).getName();
    writer.openBlock(
        "def from_dict(d: Dict[str, Any]) -> $S:",
        "",
        shapeName,
        () -> {
          writer.writeDocs(
              () -> {
                writer.write("Creates a $L from a dictionary.\n", shapeName);
                writer.write(
                    writer.formatDocs(
                        """
                        The dictionary is expected to use the modeled shape names rather \
                        than the parameter names as keys to be mostly compatible with boto3."""));
              });

          if (shape.members().isEmpty() && !isError) {
            writer.write("return $L()", shapeName);
            return;
          }

          // Block below is the only new addition to this function compared to Smithy-Python.
          // Import any modules required for reference shapes to convert from_dict.
          // Import within function to avoid circular imports from top-level imports
          for (MemberShape memberShape : shape.members()) {
            var target = model.expectShape(memberShape.getTarget());
            if (target.hasTrait(ReferenceTrait.class)) {
              Symbol targetSymbol = symbolProvider.toSymbol(target);
              writer.write(
                  "from $L import $L", targetSymbol.getNamespace(), targetSymbol.getName());
            }
          }

          if (requiredMembers.isEmpty() && !isError) {
            writer.write("kwargs: Dict[str, Any] = {}");
          } else {
            writer.openBlock(
                "kwargs: Dict[str, Any] = {",
                "}",
                () -> {
                  if (isError) {
                    writer.write("'message': d['message'],");
                  }
                  for (MemberShape member : requiredMembers) {
                    var memberName = symbolProvider.toMemberName(member);
                    var target = model.expectShape(member.getTarget());
                    Symbol targetSymbol = symbolProvider.toSymbol(target);
                    if (target.isStructureShape()) {
                      writer.write(
                          "$S: $L.from_dict(d[$S]),",
                          memberName,
                          targetSymbol.getName(),
                          member.getMemberName());
                    } else if (targetSymbol.getProperty("fromDict").isPresent()) {
                      var targetFromDictSymbol =
                          targetSymbol.expectProperty("fromDict", Symbol.class);
                      writer.write(
                          "$S: $T(d[$S]),",
                          memberName,
                          targetFromDictSymbol,
                          member.getMemberName());
                    } else {
                      writer.write("$S: d[$S],", memberName, member.getMemberName());
                    }
                  }
                });
          }
          writer.write("");

          for (MemberShape member : optionalMembers) {
            var memberName = symbolProvider.toMemberName(member);
            var target = model.expectShape(member.getTarget());
            writer.openBlock(
                "if $S in d:",
                "",
                member.getMemberName(),
                () -> {
                  var targetSymbol = symbolProvider.toSymbol(target);
                  if (target.isStructureShape()) {
                    writer.write(
                        "kwargs[$S] = $L.from_dict(d[$S])",
                        memberName,
                        targetSymbol.getName(),
                        member.getMemberName());
                  } else if (targetSymbol.getProperty("fromDict").isPresent()) {
                    var targetFromDictSymbol =
                        targetSymbol.expectProperty("fromDict", Symbol.class);
                    writer.write(
                        "kwargs[$S] = $T(d[$S]),",
                        memberName,
                        targetFromDictSymbol,
                        member.getMemberName());
                  } else {
                    writer.write("kwargs[$S] = d[$S]", memberName, member.getMemberName());
                  }
                });
          }

          writer.write("return $L(**kwargs)", shapeName);
        });
    writer.write("");
  }

  /**
   *
   * @param member
   * @param memberName
   */
  protected void writeInitMethodAssignerForRequiredMember(MemberShape member, String memberName) {
    writeInitMethodConstraintsChecksForMember(member, memberName);
    writer.write("self.$1L = $1L", memberName);
  }

  protected void writeInitMethodAssignerForOptionalMember(MemberShape member, String memberName) {
    writeInitMethodConstraintsChecksForMember(member, memberName);
    writer.write(
        "self.$1L = $1L if $1L is not None else $2L", memberName, getDefaultValue(writer, member));
  }

  protected void writeInitMethodConstraintsChecksForMember(MemberShape member, String memberName) {
    // RangeTrait
    Shape targetShape = model.expectShape(member.getTarget());
    if (targetShape.hasTrait(RangeTrait.class)) {
      RangeTrait rangeTrait = targetShape.getTrait(RangeTrait.class).get();
      if (rangeTrait.getMin().isPresent()) {
        writeRangeTraitMinCheckForMember(member, memberName, rangeTrait);
      }
      if (rangeTrait.getMax().isPresent()) {
        writeRangeTraitMaxCheckForMember(member, memberName, rangeTrait);
      }
    }

    // LengthTrait
    if (targetShape.hasTrait(LengthTrait.class)) {
      LengthTrait lengthTrait = targetShape.getTrait(LengthTrait.class).get();
      if (lengthTrait.getMin().isPresent()) {
        writeLengthTraitMinCheckForMember(memberName, lengthTrait);
      }
      if (lengthTrait.getMax().isPresent()) {
        writeLengthTraitMaxCheckForMember(memberName, lengthTrait);
      }
    }
  }

  /**
   * Write validation for {@link LengthTrait} min value. Called from __init__.
   *
   * @param memberName
   * @param lengthTrait
   */
  protected void writeLengthTraitMinCheckForMember(String memberName, LengthTrait lengthTrait) {
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
              min);
        });
  }

  /**
   * Write validation for {@link LengthTrait} max value. Called from __init__.
   *
   * @param memberName
   * @param lengthTrait
   */
  protected void writeLengthTraitMaxCheckForMember(String memberName, LengthTrait lengthTrait) {
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
              max);
        });
  }

  /**
   * Write validation for {@link RangeTrait} min value. Called from __init__.
   *
   * @param member
   * @param memberName
   * @param rangeTrait
   */
  protected void writeRangeTraitMinCheckForMember(
      MemberShape member, String memberName, RangeTrait rangeTrait) {
    String min =
        ConstrainTraitUtils.RangeTraitUtils.minAsShapeType(
            model.expectShape(member.getTarget()), rangeTrait);
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
              min);
        });
  }

  /**
   * Write validation for {@link RangeTrait} max value. Called from __init__.
   *
   * @param member
   * @param memberName
   * @param rangeTrait
   */
  protected void writeRangeTraitMaxCheckForMember(
      MemberShape member, String memberName, RangeTrait rangeTrait) {
    String max =
        ConstrainTraitUtils.RangeTraitUtils.maxAsShapeType(
            model.expectShape(member.getTarget()), rangeTrait);
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
              max);
        });
  }
}
