package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import org.assertj.core.util.Strings;
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
 * to generate code that maps a Smithy-modelled shape's internal attributes
 * to the corresponding Dafny shape's internal attributes.
 *
 * This generates code in a `smithy_to_dafny.py` file.
 * The generated code consists of methods that convert from a Smithy-modelled shape
 *   to a Dafny-modelled shape.
 * Code that requires these conversions will call out to this file.
 */
public class LocalServiceToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;
    private final String filename;

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     */
    public LocalServiceToDafnyShapeVisitor(
        GenerationContext context,
        String dataSource,
        PythonWriter writer,
        String filename
    ) {
      this.context = context;
      this.dataSource = dataSource;
      this.writer = writer;
      this.filename = filename;
    }

  public LocalServiceToDafnyShapeVisitor(
      GenerationContext context,
      String dataSource,
      PythonWriter writer
  ) {
    this.context = context;
    this.dataSource = dataSource;
    this.writer = writer;
    this.filename = "";
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
      writer.addStdlibImport("_dafny", "Seq");
      return "Seq(" + dataSource + ")";
    }

    @Override
    public String structureShape(StructureShape structureShape) {
      System.out.println("TE");
      System.out.println(structureShape.getId().getNamespace());
      System.out.println(context.settings().getService().getNamespace());
      if (structureShape.getId().getNamespace().equals(context.settings().getService().getNamespace())) {
        LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
            context, writer);
        DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape,
            context, writer);
      }

      // Import the smithy_to_dafny converter from where the ShapeVisitor was called
//      writer.addImport(".smithy_to_dafny",
//          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape));
//      writer.addImport(
//          SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
//              structureShape.getId().getNamespace(), context
//          ) + ".smithy_to_dafny",
//          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape, context)
//      );
      System.out.println("TE2");
      String pythonModuleName = SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
          structureShape.getId().getNamespace(),
          context
      );
      System.out.println(pythonModuleName);
      if (!filename.equals("smithy_to_dafny"))  {
        writer.addStdlibImport(pythonModuleName + "smithy_to_dafny");
      }

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
      return "%1$s%2$s(%3$s)".formatted(
          filename.equals("smithy_to_dafny")
              ? ""
              : pythonModuleName + ".smithy_to_dafny.",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape, context),
          dataSource
      );
    }

    @Override
    public String listShape(ListShape shape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      // Import Seq within the smithy_to_dafny conversion file
      delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", conversionWriter -> {
        conversionWriter.addStdlibImport("_dafny", "Seq");
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
              new LocalServiceToDafnyShapeVisitor(context, "list_element", writer)
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

      delegator.useFileWriter(moduleName + "/smithy_to_dafny.py", "", conversionWriter -> {
        conversionWriter.addStdlibImport("_dafny", "Map");
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
              new LocalServiceToDafnyShapeVisitor(context, "key", writer)
          )
      ));

      // Write converted map values into the map:
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)``
      builder.append("%1$s".formatted(
          valueTargetShape.accept(
              new LocalServiceToDafnyShapeVisitor(context, "value", writer)
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
      writer.addStdlibImport("_dafny", "Seq");
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
      return dataSource;
    }

    @Override
    public String unionShape(UnionShape unionShape) {
      LocalServiceToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);
      DafnyToLocalServiceConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape,
          context, writer);

      // Import the smithy_to_dafny converter from where the ShapeVisitor was called
      writer.addImport(".smithy_to_dafny",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape, context));

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape, context),
          dataSource
      );
    }
}
