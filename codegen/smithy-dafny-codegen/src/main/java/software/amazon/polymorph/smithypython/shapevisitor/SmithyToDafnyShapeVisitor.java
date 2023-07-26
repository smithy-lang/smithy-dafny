package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.shapes.BigDecimalShape;
import software.amazon.smithy.model.shapes.BigIntegerShape;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.ByteShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.EnumShape;
import software.amazon.smithy.model.shapes.FloatShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Smithy-modelled shape's internal attributes
 * to the corresponding Dafny shape's internal attributes.
 */
public class SmithyToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final PythonWriter writer;
    private final boolean isConfigShape;

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     */
    public SmithyToDafnyShapeVisitor(
        GenerationContext context,
        String dataSource,
        PythonWriter writer,
        boolean isConfigShape
    ) {
      this.context = context;
      this.dataSource = dataSource;
      this.writer = writer;
      this.isConfigShape = isConfigShape;
    }

  protected String referenceStructureShape(StructureShape shape) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    if (resourceOrService.asResourceShape().isPresent()) {
      ResourceShape resourceShape = resourceOrService.asResourceShape().get();
      DafnyNameResolver.importDafnyTypeForResourceShape(writer, resourceShape);
      return dataSource;
    }

    throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + shape);
  }

    @Override
    protected String getDefault(Shape shape) {
      var protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported conversion of %s to %s using the %s protocol",
          shape, shape.getType(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      return dataSource;
    }

    @Override
    public String structureShape(StructureShape shape) {
      if (shape.hasTrait(ReferenceTrait.class)) {
        return referenceStructureShape(shape);
      }
      DafnyNameResolver.importDafnyTypeForShape(writer, shape.getId());
      writer.addImport("Wrappers_Compile", "Option_Some");
      writer.addImport("Wrappers_Compile", "Option_None");
      StringBuilder builder = new StringBuilder();
      // Open Dafny structure shape
      // e.g.
      // DafnyStructureName(...
      builder.append("%1$s(".formatted(DafnyNameResolver.getDafnyTypeForShape(shape)));
      // Recursively dispatch a new ShapeVisitor for each member of the structure
      for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
        String memberName = memberShapeEntry.getKey();
        MemberShape memberShape = memberShapeEntry.getValue();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());

        // Adds `DafnyStructureMember=smithy_structure_member(...)`
        // e.g.
        // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
        builder.append("%1$s=".formatted(memberName));
        if (!isConfigShape && memberShape.isOptional()) {
          builder.append("((Option_Some(%1$s)) if (%2$s is not None) else (Option_None())),\n".formatted(
              targetShape.accept(
                new SmithyToDafnyShapeVisitor(
                    context,
                    dataSource + "." + CaseUtils.toSnakeCase(memberName),
                    writer,
                    isConfigShape
                )
              ),
              dataSource + "." + CaseUtils.toSnakeCase(memberName)
          ));
        } else {
          builder.append("%1$s,\n".formatted(
              targetShape.accept(
                new SmithyToDafnyShapeVisitor(
                    context,
                    dataSource + "." + CaseUtils.toSnakeCase(memberName),
                    writer,
                    isConfigShape
                )
              )
          ));
        }

//        builder.append("%1$s=%2$s%3$s%4$s,\n".formatted(
//            memberName,
//            !isConfigShape
//            memberShape.isOptional() && !isConfigShape ? "Option_Some(" : "",
//            targetShape.accept(
//                new SmithyToDafnyShapeVisitor(context,
//                        dataSource + "." + CaseUtils.toSnakeCase(memberName),
//            writer, isConfigShape)),
//            memberShape.isOptional() && !isConfigShape ? ")" : ""
//            ));
      }
      // Close structure
      return builder.append(")").toString();
    }

  @Override
  public String mapShape(MapShape shape) {
    StringBuilder builder = new StringBuilder();

    writer.addImport("_dafny", "Map");

    builder.append("Map({");
    MemberShape keyMemberShape = shape.getKey();
    final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
    MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());

    builder.append("%1$s: ".formatted(
        keyTargetShape.accept(
            new SmithyToDafnyShapeVisitor(context, "key", writer, isConfigShape)
        )
    ));

    builder.append("%1$s".formatted(
        valueTargetShape.accept(
            new SmithyToDafnyShapeVisitor(context, "value", writer, isConfigShape)
        )
    ));

    // Close structure
    return builder.append(" for (key, value) in %1$s.items() })".formatted(dataSource)).toString();
  }

    @Override
    public String listShape(ListShape shape) {

      writer.addImport("_dafny", "Seq");

      StringBuilder builder = new StringBuilder();

      builder.append("Seq([");
      MemberShape memberShape = shape.getMember();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      builder.append("%1$s".formatted(
          targetShape.accept(
              new SmithyToDafnyShapeVisitor(context, "list_element", writer, isConfigShape)
          )));

      // Close structure
      return builder.append(" for list_element in %1$s])".formatted(dataSource)).toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return dataSource;
    }

    @Override
    public String stringShape(StringShape shape) {
      return dataSource;
    }

    @Override
    public String byteShape(ByteShape shape) {
      return getDefault(shape);
    }

    @Override
    public String shortShape(ShortShape shape) {
      return getDefault(shape);
    }

    @Override
    public String integerShape(IntegerShape shape) {
      return dataSource;
    }

    @Override
    public String longShape(LongShape shape) {
      return dataSource;
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String floatShape(FloatShape shape) {
      return getDefault(shape);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      return dataSource;
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return getDefault(shape);
    }

    @Override
    public String enumShape(EnumShape shape) {
      return dataSource;
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return getDefault(shape);
    }
}
