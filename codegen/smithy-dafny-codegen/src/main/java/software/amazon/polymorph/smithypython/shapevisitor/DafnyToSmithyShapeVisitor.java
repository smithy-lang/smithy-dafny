package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
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
import software.amazon.smithy.model.shapes.Shape;
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
 * to generate code that maps a Dafny shape's internal attributes
 * to the corresponding Smithy shape's internal attributes.
 */
public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;
    private final PythonWriter writer;
    private final boolean isConfigShape;

    /**
     * @param context       The generation context.
     * @param dataSource    The in-code location of the data to provide an output of
     *                      ({@code output.foo}, {@code entry}, etc.)
     * @param writer        The PythonWriter being used
     * @param isConfigShape Flag indicating whether the shape being visited is a Config shape,
     *                      which has special logic around optional members
     */
    public DafnyToSmithyShapeVisitor(
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
      // TODO: This `models`/`client` logic seems flawed and probably needs to be revisited...
      String importFile;
      if (resourceOrService.isResourceShape()) {
        importFile = ".models";
      } else if (resourceOrService.isServiceShape()) {
        importFile = ".client";
      } else {
        throw new IllegalArgumentException("MUST be a Service or Resource: " + resourceOrService);
      }
      System.out.println("importting2");
      System.out.println(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
          resourceOrService.getId().getNamespace(), context
      ) + importFile);
      writer.addImport(
          SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
              resourceOrService.getId().getNamespace(), context
          ) + importFile,
          resourceOrService.getId().getName());
      return "%1$s(_impl=%2$s)".formatted(resourceOrService.getId().getName(), dataSource);
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
      if (!isConfigShape) {
        System.out.println("importting1");
        System.out.println(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            shape.getId().getNamespace(),
            context
        ) + ".models");

        writer.addImport(
            SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
                shape.getId().getNamespace(),
                context
            ) + ".models", shape.getId().getName());
      }

      StringBuilder builder = new StringBuilder();
      // Open Smithy structure shape
      // e.g.
      // smithy_structure_name(...
      builder.append("%1$s(".formatted(shape.getId().getName()));
      // Recursively dispatch a new ShapeVisitor for each member of the structure
      for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
        String memberName = memberShapeEntry.getKey();
        MemberShape memberShape = memberShapeEntry.getValue();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());

        // Adds `smithy_structure_member=DafnyStructureMember(...)`
        // e.g.
        // smithy_structure_name(smithy_structure_member=DafnyStructureMember(...), ...)
        builder.append("%1$s=".formatted(CaseUtils.toSnakeCase(memberName)));
        if (memberShape.isOptional()) {
          builder.append("%1$s,\n".formatted(
              targetShape.accept(
                  new DafnyToSmithyShapeVisitor(
                      context,
                      dataSource + "." + memberName + ".UnwrapOr(None)",
                      writer,
                      isConfigShape)
              )
          ));
        } else {
          builder.append("%1$s,\n".formatted(
              targetShape.accept(
                  new DafnyToSmithyShapeVisitor(
                      context,
                      dataSource + "." + memberName,
                      writer,
                      isConfigShape)
              )
          ));
        }
      }
      // Close structure
      return builder.append(")").toString();
    }

    @Override
    public String listShape(ListShape shape) {
      StringBuilder builder = new StringBuilder();

      // Open list:
      // `[`
      builder.append("[");
      MemberShape memberShape = shape.getMember();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      // Add converted list elements into the list:
      // `[list_element for list_element in `DafnyToSmithy(targetShape)``
      builder.append("%1$s".formatted(
          targetShape.accept(
              new DafnyToSmithyShapeVisitor(context, "list_element", writer, isConfigShape)
          )));

      // Close structure:
      // `[list_element for list_element in `DafnyToSmithy(targetShape)`]`
      return builder.append(" for list_element in %1$s]".formatted(dataSource)).toString();
    }

  @Override
  public String mapShape(MapShape shape) {
    StringBuilder builder = new StringBuilder();

    // Open map:
    // `{`
    builder.append("{");
    MemberShape keyMemberShape = shape.getKey();
    final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
    MemberShape valueMemberShape = shape.getValue();
    final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());

    // Write converted map keys into the map:
    // `{`DafnyToSmithy(key)`:`
    builder.append("%1$s: ".formatted(
        keyTargetShape.accept(
            new DafnyToSmithyShapeVisitor(context, "key", writer, isConfigShape)
        )
    ));

    // Write converted map values into the map:
    // `{`DafnyToSmithy(key)`: `DafnyToSmithy(value)``
    builder.append("%1$s".formatted(
        valueTargetShape.accept(
            new DafnyToSmithyShapeVisitor(context, "value", writer, isConfigShape)
        )
    ));

    // Complete map comprehension and close map
    // `{`DafnyToSmithy(key)`: `DafnyToSmithy(value)`` for (key, value) in `dataSource`.items }`
    // No () on items call; `dataSource` is a Dafny map, where `items` is a @property and not a method.
    return builder.append(" for (key, value) in %1$s.items }".formatted(dataSource)).toString();
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
