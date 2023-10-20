package software.amazon.polymorph.smithypython.awssdk.shapevisitor;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters.AwsSdkToDafnyConversionFunctionWriter;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters.DafnyToAwsSdkConversionFunctionWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
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

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a AWS SDK kwarg-indexed dictionary
 * to the corresponding Dafny shape's internal attributes.
 */
public class AwsSdkToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     * @param writer A PythonWriter pointing to the in-code location where the
     *               root
     */
    public AwsSdkToDafnyShapeVisitor(
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
      return "Seq(" + dataSource + ")";
    }

    @Override
    public String structureShape(StructureShape structureShape) {
      // Dafny does not generate a type for Unit shape
      if (Utils.isUnitShape(structureShape.getId())) {
        return "None";
      }

      AwsSdkToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
          context, writer);
      DafnyToAwsSdkConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
          context, writer);

      // Import the aws_sdk_to_dafny converter from where the ShapeVisitor was called
      writer.addImport(".aws_sdk_to_dafny",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(structureShape));

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
      return "%1$s(%2$s)".formatted(
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(structureShape),
          dataSource
      );
    }

    @Override
    public String listShape(ListShape shape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      // Import Seq within the aws_sdk_to_dafny conversion file
      delegator.useFileWriter(moduleName + "/aws_sdk_to_dafny.py", "", conversionWriter -> {
        conversionWriter.addStdlibImport("_dafny", "Seq");
        writer.addStdlibImport("_dafny", "Seq");
      });

      StringBuilder builder = new StringBuilder();

      // Open Dafny sequence:
      // `Seq([`
      builder.append("Seq([");
      MemberShape memberShape = shape.getMember();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      // Add converted list elements into the list:
      // `Seq([`SmithyToDafny(list_element)``
      builder.append("%1$s".formatted(
          targetShape.accept(
              new AwsSdkToDafnyShapeVisitor(context, "list_element", writer)
          )));

      // Close structure
      // `Seq([`SmithyToDafny(list_element)` for list_element in `dataSource`])``
      return builder.append(" for list_element in %1$s])".formatted(dataSource)).toString();
    }

    @Override
    public String mapShape(MapShape shape) {
      StringBuilder builder = new StringBuilder();
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      delegator.useFileWriter(moduleName + "/aws_sdk_to_dafny.py", "", conversionWriter -> {
        conversionWriter.addStdlibImport("_dafny", "Map");
        writer.addStdlibImport("_dafny", "Map");
      });

      // Open Dafny map:
      // `Map({`
      builder.append("Map({");
      MemberShape keyMemberShape = shape.getKey();
      final Shape keyTargetShape = context.model().expectShape(keyMemberShape.getTarget());
      MemberShape valueMemberShape = shape.getValue();
      final Shape valueTargetShape = context.model().expectShape(valueMemberShape.getTarget());

      // Write converted map keys into the map:
      // `{`SmithyToDafny(key)`:`
      builder.append("%1$s: ".formatted(
          keyTargetShape.accept(
              new AwsSdkToDafnyShapeVisitor(context, "key", writer)
          )
      ));

      // Write converted map values into the map:
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)``
      builder.append("%1$s".formatted(
          valueTargetShape.accept(
              new AwsSdkToDafnyShapeVisitor(context, "value", writer)
          )
      ));

      // Complete map comprehension and close map
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)`` for (key, value) in `dataSource`.items() }`
      return builder.append(" for (key, value) in %1$s.items() })".formatted(dataSource)).toString();
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return dataSource;
    }

    @Override
    public String stringShape(StringShape shape) {
      return "Seq(" + dataSource + ")";
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
      // TODO-Python: BLOCKING: This lets code generate, but will fail when code hits it
      return "TypeError(\"TimestampShape not supported\")";
    }

    @Override
    public String unionShape(UnionShape unionShape) {
      DafnyToAwsSdkConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);
      AwsSdkToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);

      // Import the aws_sdk_to_dafny converter from where the ShapeVisitor was called
      writer.addImport(".aws_sdk_to_dafny",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(unionShape));

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `AwsSdkToDafny_example_namespace_ExampleShape(input)`
      return "%1$s(%2$s)".formatted(
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(unionShape),
          dataSource
      );
    }
}
