package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;
import static software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver.isAwsSdkShape;

import java.util.Set;
import java.util.stream.Stream;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.ConstraintUtils;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.NullableIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.*;
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
public class DafnyPythonLocalServiceStructureGenerator
  extends StructureGenerator {

  public DafnyPythonLocalServiceStructureGenerator(
    Model model,
    PythonSettings settings,
    SymbolProvider symbolProvider,
    PythonWriter writer,
    StructureShape shape,
    Set<Shape> recursiveShapes
  ) {
    super(model, settings, symbolProvider, writer, shape, recursiveShapes);
  }

  @Override
  public void run() {
    Set<ShapeId> localServiceConfigShapes =
      SmithyNameResolver.getLocalServiceConfigShapes(model);

    if (shape.hasTrait(PositionalTrait.class)) {
      // Do not need to render shapes with positional trait, their linked shapes are rendered
      return;
    } else if (localServiceConfigShapes.contains(shape.getId())) {
      renderLocalServiceConfigShape();
    } else if (!shape.hasTrait(ErrorTrait.class)) {
      renderStructure();
    } else {
      renderError();
    }
  }

  /**
   * Renders a LocalService's Config shape in config.py.
   * LocalService Config shapes are special:
   * - They extend the default Smithy-Python Config
   * - Their __init__ methods call super.__init__() to init Smithy-Python Config.
   * Most of this is lifted directly from Smithy-Python; the changed components are
   * called out with comments saying "Component below is changed from Smithy-Python."
   */
  protected void renderLocalServiceConfigShape() {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    var symbol = symbolProvider.toSymbol(shape);
    // Component below is changed from Smithy-Python.
    // Write special class that extends parent class.
    writer.openBlock(
      "class $L(Config):",
      "",
      symbol.getName(),
      () -> {
        writeProperties(false);
        // Component below is changed from Smithy-Python.
        // Write special __init__ that initializes parent class.
        writeLocalServiceConfigShapeInit();
        writeAsDict(false);
        writeFromDict(false);
        writeRepr(false);
        writeEq(false);
      }
    );
    writer.write("");
  }

  /**
   * Writes an __init__ method for a LocalService Config shape.
   * Most of this is lifted directly from Smithy-Python; the changed components are
   * called out with comments saying "Component below is changed from Smithy-Python."
   */
  protected void writeLocalServiceConfigShapeInit() {
    writer.openBlock(
      "def __init__(",
      "):",
      () -> {
        writer.write("self,");
        if (!shape.members().isEmpty()) {
          // Adding this star to the front prevents the use of positional arguments.
          writer.write("*,");
        }
        for (MemberShape member : requiredMembers) {
          writeInitMethodParameterForRequiredMember(false, member);
        }
        for (MemberShape member : optionalMembers) {
          writeInitMethodParameterForOptionalMember(false, member);
        }
      }
    );

    writer.indent();

    // This is Smithy-Python's writeClassDocs modified for LocalService Config shapes.
    this.writer.writeDocs(() -> {
        if (shape.hasTrait(DocumentationTrait.class)) {
          this.shape.getTrait(DocumentationTrait.class)
            .ifPresent(trait -> {
              this.writer.write(
                  this.writer.formatDocs(trait.getValue()),
                  new Object[0]
                );
            });
        } else {
          // Component below is changed from Smithy-Python.
          // Write default docstring for LocalService Config shape constructor
          this.writer.write(
              "Constructor for $L",
              symbolProvider.toSymbol(shape).getName()
            );
        }

        if (!this.shape.members().isEmpty()) {
          this.writer.write("", new Object[0]);
          this.requiredMembers.forEach(this::writeMemberDocs);
          this.optionalMembers.forEach(this::writeMemberDocs);
        }
      });
    // Component below is changed from Smithy-Python.
    // Initialize parent Config.
    writer.write("super().__init__()");

    Stream
      .concat(requiredMembers.stream(), optionalMembers.stream())
      .forEach(member -> {
        String memberName = symbolProvider.toMemberName(member);
        if (isOptionalDefault(member)) {
          writeInitMethodAssignerForOptionalMember(member, memberName);
        } else {
          writeInitMethodAssignerForRequiredMember(member, memberName);
        }
      });
    writer.dedent();
    writer.write("");
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
    var apiError = Symbol
      .builder()
      .name("ApiError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            settings.getService().getNamespace(),
            settings
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            settings.getService().getNamespace()
          )
        )
      )
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
      }
    );
    writer.write("");
  }

  /**
   * Override Smithy-Python to not unambiguously write a `message`
   * attribute on errors;
   * Smithy-Dafny defines this attribute on its errors,
   * so Smithy-Python behavior is changed to not write `message` multiple times.
   * (In particular, OpaqueErrors may not have a `message` attribute,
   * which leads to issues.)
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
          trailingComma
        );
      } else {
        writer.write(
          """
          if self.$1L is not None:
              result += f"$1L={repr(self.$1L)}$2L"
          """,
          memberName,
          trailingComma
        );
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
  protected void writePropertyForMember(
    boolean isError,
    MemberShape memberShape
  ) {
    Shape target = model.expectShape(memberShape.getTarget());
    String memberName = symbolProvider.toMemberName(memberShape);

    if (
      target.isListShape() &&
      model
        .expectShape(target.asListShape().get().getMember().getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      Shape listMemberShape = model.expectShape(
        target.asListShape().get().getMember().getTarget()
      );
      Shape referentShape = model.expectShape(
        listMemberShape.expectTrait(ReferenceTrait.class).getReferentId()
      );
      Symbol targetSymbol = symbolProvider.toSymbol(referentShape);

      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: list['$L']";
      writer.write(
        formatString,
        memberName,
        targetSymbol.getNamespace() + "." + targetSymbol.getName()
      );
      return;
    }

    // We currently don't have any map shapes that have values with reference traits;
    // once we do, this needs to be filled in
    if (
      target.isMapShape() &&
      model
        .expectShape(target.asMapShape().get().getValue().getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      throw new IllegalArgumentException(
        "Map shapes containing references currently unsupported: " + target
      );
    }

    // Reference shapes require forward reference to avoid circular import,
    // but references to AWS SDKs don't
    if (
      target.hasTrait(ReferenceTrait.class) &&
      !AwsSdkNameResolver.isAwsSdkShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      )
    ) {
      Shape referentShape = model.expectShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      );

      NullableIndex index = NullableIndex.of(model);

      if (index.isMemberNullable(memberShape)) {
        writer.addStdlibImport("typing", "Optional");
        // Use forward reference for reference traits to avoid circular import
        String formatString = "$L: Optional['$L']";
        writer.write(
          formatString,
          memberName,
          symbolProvider.toSymbol(referentShape).getNamespace() +
          "." +
          symbolProvider.toSymbol(referentShape).getName()
        );
        writer.addStdlibImport(
          symbolProvider.toSymbol(referentShape).getNamespace()
        );
      } else {
        // Use forward reference for reference traits to avoid circular import,
        String formatString = "$L: '$L'";
        writer.write(
          formatString,
          memberName,
          symbolProvider.toSymbol(referentShape).getNamespace() +
          "." +
          symbolProvider.toSymbol(referentShape).getName()
        );
        writer.addStdlibImport(
          symbolProvider.toSymbol(referentShape).getNamespace()
        );
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
    boolean isError,
    MemberShape memberShape
  ) {
    Shape target = model.expectShape(memberShape.getTarget());
    String memberName = symbolProvider.toMemberName(memberShape);

    if (
      target.isListShape() &&
      model
        .expectShape(target.asListShape().get().getMember().getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      Shape listMemberShape = model.expectShape(
        target.asListShape().get().getMember().getTarget()
      );
      Shape referentShape = model.expectShape(
        listMemberShape.expectTrait(ReferenceTrait.class).getReferentId()
      );
      Symbol targetSymbol = symbolProvider.toSymbol(referentShape);

      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: list['$L'],";
      writer.write(
        formatString,
        memberName,
        targetSymbol.getNamespace() + "." + targetSymbol.getName()
      );
      return;
    }

    // We currently don't have any map shapes that have values with reference traits;
    // once we do, this needs to be filled in
    if (
      target.isMapShape() &&
      model
        .expectShape(target.asMapShape().get().getValue().getTarget())
        .hasTrait(ReferenceTrait.class)
    ) {
      throw new IllegalArgumentException(
        "Map shapes containing references currently unsupported: " + target
      );
    }

    // Reference shapes require forward reference to avoid circular import,
    // but references to AWS SDKs don't
    if (
      target.hasTrait(ReferenceTrait.class) &&
      !AwsSdkNameResolver.isAwsSdkShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      )
    ) {
      Shape referentShape = model.expectShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      );
      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: '$L',";
      writer.write(
        formatString,
        memberName,
        symbolProvider.toSymbol(referentShape).getNamespace() +
        "." +
        symbolProvider.toSymbol(referentShape).getName()
      );
      writer.addStdlibImport(
        symbolProvider.toSymbol(referentShape).getNamespace()
      );
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
    boolean isError,
    MemberShape memberShape
  ) {
    Shape target = model.expectShape(memberShape.getTarget());

    // Reference shapes require forward reference to avoid circular import,
    // but references to AWS SDKs don't
    if (
      target.hasTrait(ReferenceTrait.class) &&
      !AwsSdkNameResolver.isAwsSdkShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      )
    ) {
      Shape referentShape = model.expectShape(
        target.expectTrait(ReferenceTrait.class).getReferentId()
      );
      String memberName = symbolProvider.toMemberName(memberShape);

      writer.addStdlibImport("typing", "Optional");
      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: Optional['$L'] = None,";
      writer.write(
        formatString,
        memberName,
        symbolProvider.toSymbol(referentShape).getNamespace() +
        "." +
        symbolProvider.toSymbol(referentShape).getName()
      );
      writer.addStdlibImport(
        symbolProvider.toSymbol(referentShape).getNamespace()
      );
    } else {
      super.writeInitMethodParameterForOptionalMember(isError, memberShape);
    }
  }

  /**
   * Override Smithy-Python writeFromDict to handle shapes with {@link ReferenceTrait}s.
   * Most of this is lifted directly from Smithy-Python; the changed components are
   * called out with comments saying "Block below is changed from Smithy-Python."
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
        writer.writeDocs(() -> {
          writer.write("Creates a $L from a dictionary.\n", shapeName);
        });

        if (shape.members().isEmpty() && !isError) {
          writer.write("return $L()", shapeName);
          return;
        }

        // Block below is changed from Smithy-Python.
        // Import any modules required for reference shapes to convert from_dict.
        // Import within function to avoid circular imports from top-level imports
        for (MemberShape memberShape : shape.members()) {
          var target = model.expectShape(memberShape.getTarget());
          // Reference shapes require forward reference to avoid circular import,
          // but references to AWS SDKs don't
          if (
            target.hasTrait(ReferenceTrait.class) &&
            !AwsSdkNameResolver.isAwsSdkShape(
              target.getTrait(ReferenceTrait.class).get().getReferentId()
            )
          ) {
            Symbol targetSymbol = symbolProvider.toSymbol(target);
            writer.write(
              "from $L import $L",
              targetSymbol.getNamespace(),
              targetSymbol.getName()
            );
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
                // Block below is changed from Smithy-Python.
                // If passing a boto3 client, just pass the client.
                // Also, use snakecase member name inside the dictionary.
                if (
                  target.hasTrait(ReferenceTrait.class) &&
                  target.expectTrait(ReferenceTrait.class).isService() &&
                  isAwsSdkShape(
                    target.expectTrait(ReferenceTrait.class).getReferentId()
                  )
                ) {
                  writer.write("$S: d[$S],", memberName, memberName);
                } else if (target.isStructureShape()) {
                  writer.write(
                    "$S: $L.from_dict(d[$S]),",
                    memberName,
                    targetSymbol.getName(),
                    memberName
                  );
                } else if (targetSymbol.getProperty("fromDict").isPresent()) {
                  var targetFromDictSymbol = targetSymbol.expectProperty(
                    "fromDict",
                    Symbol.class
                  );
                  writer.write(
                    "$S: $T(d[$S]),",
                    memberName,
                    targetFromDictSymbol,
                    memberName
                  );
                } else {
                  writer.write("$S: d[$S],", memberName, memberName);
                }
              }
            }
          );
        }
        writer.write("");

        for (MemberShape member : optionalMembers) {
          var memberName = symbolProvider.toMemberName(member);
          var target = model.expectShape(member.getTarget());
          writer.openBlock(
            "if $S in d:",
            "",
            memberName,
            () -> {
              var targetSymbol = symbolProvider.toSymbol(target);
              // Block below is changed from Smithy-Python.
              // If passing a boto3 client, just pass the client.
              // Also, use snakecase member name inside the dictionary.
              if (
                target.hasTrait(ReferenceTrait.class) &&
                target.expectTrait(ReferenceTrait.class).isService() &&
                isAwsSdkShape(
                  target.expectTrait(ReferenceTrait.class).getReferentId()
                )
              ) {
                writer.write("kwargs[$S] = d[$S]", memberName, memberName);
              } else if (target.isStructureShape()) {
                writer.write(
                  "kwargs[$S] = $L.from_dict(d[$S])",
                  memberName,
                  targetSymbol.getName(),
                  memberName
                );
              } else if (targetSymbol.getProperty("fromDict").isPresent()) {
                var targetFromDictSymbol = targetSymbol.expectProperty(
                  "fromDict",
                  Symbol.class
                );
                writer.write(
                  "kwargs[$S] = $T(d[$S]),",
                  memberName,
                  targetFromDictSymbol,
                  memberName
                );
              } else {
                writer.write("kwargs[$S] = d[$S]", memberName, memberName);
              }
            }
          );
        }

        writer.write("return $L(**kwargs)", shapeName);
      }
    );
    writer.write("");
  }

  /**
   * Override Smithy-Python writeAsDict to handle shapes with {@link ReferenceTrait}s.
   * Most of this is lifted directly from Smithy-Python; the changed components are
   * called out with comments saying "Block below is changed from Smithy-Python."
   *
   * @param isError
   */
  protected void writeAsDict(boolean isError) {
    writer.openBlock(
      "def as_dict(self) -> Dict[str, Any]:",
      "",
      () -> {
        writer.writeDocs(() -> {
          writer.write(
            "Converts the $L to a dictionary.\n",
            symbolProvider.toSymbol(shape).getName()
          );
        });

        // If there aren't any optional members, it's best to return immediately.
        String dictPrefix = optionalMembers.isEmpty()
          ? "return"
          : "d: Dict[str, Any] =";
        if (requiredMembers.isEmpty() && !isError) {
          writer.write("$L {}", dictPrefix);
        } else {
          writer.openBlock(
            "$L {",
            "}",
            dictPrefix,
            () -> {
              if (isError) {
                writer.write("'message': self.message,");
                writer.write("'code': self.code,");
              }
              for (MemberShape member : requiredMembers) {
                var memberName = symbolProvider.toMemberName(member);
                var target = model.expectShape(member.getTarget());
                var targetSymbol = symbolProvider.toSymbol(target);
                // Block below is changed from Smithy-Python.
                // If passing a boto3 client, just pass the client.
                // Also, use snakecase member name inside the dictionary.
                if (
                  target.hasTrait(ReferenceTrait.class) &&
                  target.expectTrait(ReferenceTrait.class).isService() &&
                  isAwsSdkShape(
                    target.expectTrait(ReferenceTrait.class).getReferentId()
                  )
                ) {
                  writer.write("$S: self.$L,", memberName, memberName);
                } else if (target.isStructureShape() || target.isUnionShape()) {
                  writer.write(
                    "$S: self.$L.as_dict(),",
                    memberName,
                    memberName
                  );
                } else if (targetSymbol.getProperty("asDict").isPresent()) {
                  var targetAsDictSymbol = targetSymbol.expectProperty(
                    "asDict",
                    Symbol.class
                  );
                  writer.write(
                    "$S: $T(self.$L),",
                    memberName,
                    targetAsDictSymbol,
                    memberName
                  );
                } else {
                  writer.write("$S: self.$L,", memberName, memberName);
                }
              }
            }
          );
        }

        if (!optionalMembers.isEmpty()) {
          writer.write("");
          for (MemberShape member : optionalMembers) {
            var memberName = symbolProvider.toMemberName(member);
            var target = model.expectShape(member.getTarget());
            var targetSymbol = symbolProvider.toSymbol(target);
            writer.openBlock(
              "if self.$1L is not None:",
              "",
              memberName,
              () -> {
                // Block below is changed from Smithy-Python.
                // If passing a boto3 client, just pass the client.
                // Also, use snakecase member name inside the dictionary.
                if (
                  target.hasTrait(ReferenceTrait.class) &&
                  target.expectTrait(ReferenceTrait.class).isService() &&
                  isAwsSdkShape(
                    target.expectTrait(ReferenceTrait.class).getReferentId()
                  )
                ) {
                  writer.write("d[$S] = self.$L", memberName, memberName);
                } else if (target.isStructureShape() || target.isUnionShape()) {
                  writer.write(
                    "d[$S] = self.$L.as_dict()",
                    memberName,
                    memberName
                  );
                } else if (targetSymbol.getProperty("asDict").isPresent()) {
                  var targetAsDictSymbol = targetSymbol.expectProperty(
                    "asDict",
                    Symbol.class
                  );
                  writer.write(
                    "d[$S] = $T(self.$L),",
                    memberName,
                    targetAsDictSymbol,
                    memberName
                  );
                } else {
                  writer.write("d[$S] = self.$L", memberName, memberName);
                }
              }
            );
          }
          writer.write("return d");
        }
      }
    );
    writer.write("");
  }

  /**
   * Write assignment from __init__ method parameter to new object's required attribute.
   * Writes any constraint-checking code before writing assignment.
   * @param member
   * @param memberName
   */
  protected void writeInitMethodAssignerForRequiredMember(
    MemberShape member,
    String memberName
  ) {
    ConstraintUtils.writeInitMethodConstraintsChecksForMember(
      writer,
      model,
      member,
      memberName
    );
    writer.write("self.$1L = $1L", memberName);
  }

  /**
   * Write assignment from __init__ method parameter to new object's optional attribute.
   * Writes any constraint-checking code before writing assignment.
   * @param member
   * @param memberName
   */
  protected void writeInitMethodAssignerForOptionalMember(
    MemberShape member,
    String memberName
  ) {
    ConstraintUtils.writeInitMethodConstraintsChecksForMember(
      writer,
      model,
      member,
      memberName
    );
    writer.write(
      "self.$1L = $1L if $1L is not None else $2L",
      memberName,
      getDefaultValue(writer, member)
    );
  }
}
