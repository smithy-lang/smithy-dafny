package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.Set;

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
      // TODO-Python: I don't think I need to render any part of positionals?
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
    // TODO: Implement protocol-level customization of the error code
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
        String formatString = format("$L: Optional[$T]", symbolProvider.toSymbol(referentShape));
        writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape));
      } else {
        String formatString = format("$L: $T",  symbolProvider.toSymbol(referentShape));
        writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape));
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

      String formatString = "$L: $T,";
      writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape));
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
      String formatString = "$L: Optional[$T] = None,";
      writer.write(formatString, memberName, symbolProvider.toSymbol(referentShape));
    } else {
      super.writeInitMethodParameterForOptionalMember(isError, memberShape);
    }
  }
}
