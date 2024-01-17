package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.Set;

import org.assertj.core.util.Strings;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.NullableIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.StructureGenerator;

/**
 * Override Smithy-Python's StructureGenerator
 * to support namespaces in other modules.
 */
public class DafnyPythonLocalServiceStructureGenerator extends StructureGenerator  {

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
    if (shape.hasTrait(PositionalTrait.class)) {
      // Do not need to render shapes with positional trait
      return;
    }
    if (!shape.hasTrait(ErrorTrait.class)) {
      renderStructure();
    } else {
      renderError();
    }
  }

  @Override
  protected void renderError() {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    writer.addStdlibImport("typing", "Literal");
    var code = shape.getId().getName();
    var symbol = symbolProvider.toSymbol(shape);
    var apiError = Symbol.builder()
            .name("ApiError")
            .namespace(format("%s.errors", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), settings)), ".")
            .definitionFile(format("./%s/errors.py", SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
            .build();
    writer.openBlock("class $L($T[Literal[$S]]):", "", symbol.getName(), apiError, code, () -> {
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

  @Override
  protected void writePropertyForMember(boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape = model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      String memberName = symbolProvider.toMemberName(memberShape);

      NullableIndex index = NullableIndex.of(model);

      if (index.isMemberNullable(memberShape)) {
        writer.addStdlibImport("typing", "Optional");
        // Use forward reference for reference traits to avoid circular import
        //   and do not import the symbol to avoid circular import
        String formatString = "$L: Optional['$L']";
        writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape).getNamespace() + "." + symbolProvider.toSymbol(referentShape).getName());
        writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());

      } else {
        // Use forward reference for reference traits to avoid circular import,
        //   and do not import the symbol to avoid circular import
        String formatString = "$L: '$L'";
        writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape).getNamespace() + "." + symbolProvider.toSymbol(referentShape).getName());
        writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());

      }
    } else {
      super.writePropertyForMember(isError, memberShape);
    }
  }

  @Override
  protected void writeInitMethodParameterForRequiredMember(boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape = model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      String memberName = symbolProvider.toMemberName(memberShape);
      // Use forward reference for reference traits to avoid circular import
      //   and do not import the symbol to avoid circular import
      String formatString = "$L: '$L',";
      writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape).getNamespace() + "." + symbolProvider.toSymbol(referentShape).getName());
      writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
    } else {
      super.writeInitMethodParameterForRequiredMember(isError, memberShape);
    }
  }

  @Override
  protected void writeInitMethodParameterForOptionalMember(boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape = model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      String memberName = symbolProvider.toMemberName(memberShape);

      writer.addStdlibImport("typing", "Optional");
      // Use forward reference for reference traits to avoid circular import
      String formatString = "$L: Optional['$L'] = None,";
      writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape).getNamespace() + "." + symbolProvider.toSymbol(referentShape).getName());
      writer.addStdlibImport(symbolProvider.toSymbol(referentShape).getNamespace());
    } else {
      super.writeInitMethodParameterForOptionalMember(isError, memberShape);
    }
  }

//  // Do not write `from_dict` methods on structures.
//  // This can introduce circular dependencies if a structure has a reference shape.
//  protected void writeFromDict(boolean isError) {
//    if (isError) {
//      super.writeFromDict(isError);
//    }
//  }

  /**
   * Override Smithy-Python writeFromDict to handle importing reference modules to avoid circular imports.
   * @param isError
   */
  protected void writeFromDict(boolean isError) {
    writer.write("@staticmethod");
    var shapeName = symbolProvider.toSymbol(shape).getName();
    writer.openBlock("def from_dict(d: Dict[str, Any]) -> $S:", "", shapeName, () -> {
      writer.writeDocs(() -> {
        writer.write("Creates a $L from a dictionary.\n", shapeName);
        writer.write(writer.formatDocs("""
                        The dictionary is expected to use the modeled shape names rather \
                        than the parameter names as keys to be mostly compatible with boto3."""));
      });

      if (shape.members().isEmpty() && !isError) {
        writer.write("return $L()", shapeName);
        return;
      }

      // Import any modules required for reference shapes to convert from_dict
      // Import within function to avoid circular imports from top-level imports
      for (MemberShape memberShape : shape.members()) {
        var target = model.expectShape(memberShape.getTarget());
        if (target.hasTrait(ReferenceTrait.class)) {
          Symbol targetSymbol = symbolProvider.toSymbol(target);
          writer.write("from $L import $L", targetSymbol.getNamespace(), targetSymbol.getName());
        }
      }

      if (requiredMembers.isEmpty() && !isError) {
        writer.write("kwargs: Dict[str, Any] = {}");
      } else {
        writer.openBlock("kwargs: Dict[str, Any] = {", "}", () -> {
          if (isError) {
            writer.write("'message': d['message'],");
          }
          for (MemberShape member : requiredMembers) {
            var memberName = symbolProvider.toMemberName(member);
            var target = model.expectShape(member.getTarget());
            Symbol targetSymbol = symbolProvider.toSymbol(target);
            if (target.isStructureShape()) {
              writer.write("$S: $L.from_dict(d[$S]),", memberName, targetSymbol.getName(), member.getMemberName());
            } else if (targetSymbol.getProperty("fromDict").isPresent()) {
              var targetFromDictSymbol = targetSymbol.expectProperty("fromDict", Symbol.class);
              writer.write("$S: $T(d[$S]),", memberName, targetFromDictSymbol, member.getMemberName());
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
        writer.openBlock("if $S in d:", "", member.getMemberName(), () -> {
          var targetSymbol = symbolProvider.toSymbol(target);
          if (target.isStructureShape()) {
            writer.write("kwargs[$S] = $L.from_dict(d[$S])", memberName, targetSymbol.getName(),
                    member.getMemberName());
          } else if (targetSymbol.getProperty("fromDict").isPresent()) {
            var targetFromDictSymbol = targetSymbol.expectProperty("fromDict", Symbol.class);
            writer.write("kwargs[$S] = $T(d[$S]),", memberName, targetFromDictSymbol,
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

  // Do not write `from_dict` methods on structures.
  // This can introduce circular dependencies if a structure has a reference shape.
//  protected void writeAsDict(boolean isError) {
//    if (isError) {
//      super.writeAsDict(isError);
//    }
//  }
}
