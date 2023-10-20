package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter.DafnyToLocalServiceConversionFunctionWriter;
import software.amazon.polymorph.smithypython.localservice.shapevisitor.conversionwriter.LocalServiceToDafnyConversionFunctionWriter;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.WriterDelegator;
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
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Dafny shape's internal attributes
 * to the corresponding Smithy shape's internal attributes.
 *
 * This generates code in a `dafny_to_smithy.py` file.
 * The generated code consists of methods that convert from a Dafny-modelled shape
 *   to a Smithy-modelled shape.
 * Code that requires these conversions will call out to this file.
 *
 * Note that the `dafny_to_smithy.py` file this generates SHOULD NOT be imported at the top-level.
 * Doing so introduces circular import dependencies, which Python cannot handle.
 * To work around this, this file SHOULD be used by importing it within function code
 *   immediately before it is used.
 * (The circular dependency occurs when dafny_to_smithy imports the shapes it is converting to,
 *  but the files those shapes are in contain logic to call dafny_to_smithy.
 *  These files are resource shapes, service shapes, and config shapes.
 *  This is unavoidable. (dafny_to_smithy MUST know about the shapes it is converting to,
 *    and the functions in these files MUST call out to dafny_to_smithy.)
 * (An alternative that is NOT implemented is to import shapes being converted at runtime,
 *  rather than importing dafny_to_smithy at runtime.
 *  This is not preferred, as it would defer many more imports to runtime.
 *  Deferring imports defers detection of issues with imported files;
 *  deferring imports on a shape-by-shape basis will defer detection of issues with those shapes;
 *  by having all deferred imports refer to the same file, the risk is mitigated.)
 */
public class DafnyToLocalServiceShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;
    /**
     * @param context     The generation context.
     * @param dataSource  The in-code location of the data to provide an output of
     *                    ({@code output.foo}, {@code entry}, etc.)
     * @param writer      The PythonWriter being used
     */
    public DafnyToLocalServiceShapeVisitor(
        GenerationContext context,
        String dataSource,
        PythonWriter writer
    ) {
      this.context = context;
      this.dataSource = dataSource;
      this.writer = writer;
    }

    @Override
    protected String getDefault(Shape shape) {
      String protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported conversion of %s to %s using the %s protocol",
          shape, shape.getType(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      return dataSource;
    }

    @Override
    public String structureShape(StructureShape structureShape) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
          context, writer);
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
          context, writer);

      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(structureShape),
          Utils.isUnitShape(structureShape.getId()) ? "" : dataSource
      );
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
              new DafnyToLocalServiceShapeVisitor(context, "list_element", writer)
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
            new DafnyToLocalServiceShapeVisitor(context, "key", writer)
        )
    ));

    // Write converted map values into the map:
    // `{`DafnyToSmithy(key)`: `DafnyToSmithy(value)``
    builder.append("%1$s".formatted(
        valueTargetShape.accept(
            new DafnyToLocalServiceShapeVisitor(context, "value", writer)
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
      return dataSource;
    }

    @Override
    public String unionShape(UnionShape unionShape) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);

      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(unionShape),
          dataSource
      );
    }

}
