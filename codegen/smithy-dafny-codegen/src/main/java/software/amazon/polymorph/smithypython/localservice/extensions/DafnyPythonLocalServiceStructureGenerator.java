package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.ArrayList;
import java.util.Set;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.NullableIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.DefaultTrait;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.StructureGenerator;

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
  protected void writePropertyForMember(boolean isError, MemberShape memberShape) {
    Shape target = model.expectShape(memberShape.getTarget());

    if (target.hasTrait(ReferenceTrait.class)) {
      Shape referentShape = model.expectShape(target.expectTrait(ReferenceTrait.class).getReferentId());
      String memberName = symbolProvider.toMemberName(memberShape);

      System.out.println("writeproperty " + referentShape.getId());

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
