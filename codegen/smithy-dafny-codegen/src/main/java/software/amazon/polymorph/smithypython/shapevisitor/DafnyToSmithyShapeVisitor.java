package software.amazon.polymorph.smithypython.shapevisitor;

import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.shapes.BigDecimalShape;
import software.amazon.smithy.model.shapes.BigIntegerShape;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.ByteShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.FloatShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Dafny shape's internal attributes
 * to the corresponding Smithy shape's internal attributes.
 */
public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final String dataSource;

    /**
     * @param context    The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code output.foo}, {@code entry}, etc.)
     */
    public DafnyToSmithyShapeVisitor(
        GenerationContext context,
        String dataSource
    ) {
      this.context = context;
      this.dataSource = dataSource;
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
      return getDefault(shape);
    }

    @Override
    public String structureShape(StructureShape shape) {

      String out = "";
      // TODO: Change fstring to support >1 shape
      for (String memberName : shape.getMemberNames()) {
        // TODO: Need to refactor entire class
        out += "%1$s=%2$s.%3$s,\n".formatted(CaseUtils.toSnakeCase(memberName), dataSource,
            memberName);
      }
      return out;
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return getDefault(shape);
    }

    @Override
    public String stringShape(StringShape shape) {
      return getDefault(shape);
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
      return getDefault(shape);
    }

    @Override
    public String longShape(LongShape shape) {
      return getDefault(shape);
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
      return getDefault(shape);
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return getDefault(shape);
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return getDefault(shape);
    }
}
