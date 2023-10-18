package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.shapevisitor.conversionwriters.AwsSdkToDafnyConversionFunctionWriter;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
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
 * to generate code that maps a Smithy-modelled shape's internal attributes
 * to the corresponding Dafny shape's internal attributes.
 *
 * This generates code in a `aws_sdk_to_dafny.py` file.
 * The generated code consists of methods that convert from a Smithy-modelled shape
 *   to a Dafny-modelled shape.
 * Code that requires these conversions will call out to this file.
 */
public class AwsSdkToDafnyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;
    private final String filename;
    private final AwsSdkToDafnyConversionFunctionWriter awsSdkToDafnyConversionFunctionWriter
        = AwsSdkToDafnyConversionFunctionWriter.getWriter();
//    // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
//    // have already generated a conversion function, so we only write each conversion function once.
//    static final Set<Shape> generatedShapes = new HashSet<>();
//  // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
//  // have already generated a conversion function, so we only write each conversion function once.
//  static final List<Shape> shapesToGenerate = new ArrayList<>();
//  static boolean generating = false;

    /**
     * @param context The generation context.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     */
    public AwsSdkToDafnyShapeVisitor(
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

    /*
    if "S" in input.keys():
      AttributeValue_union_value = AttributeValue_S(Seq(input["S"]))
     */

    @Override
    public String structureShape(StructureShape structureShape) {
      awsSdkToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(structureShape, context, writer, filename);

      // Import the aws_sdk_to_dafny converter from where the ShapeVisitor was called
      writer.addImport(".aws_sdk_to_dafny",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape));

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape),
          dataSource
      );
    }

  public void writeStructureShapeConverter(StructureShape shape) {

  }



    @Override
    public String listShape(ListShape shape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      // Import Seq within the aws_sdk_to_dafny conversion file
      delegator.useFileWriter(moduleName + "/aws_sdk_to_dafny.py", "", conversionWriter -> {
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
              new AwsSdkToDafnyShapeVisitor(context, "list_element", writer, filename)
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
              new AwsSdkToDafnyShapeVisitor(context, "key", writer, filename)
          )
      ));

      // Write converted map values into the map:
      // `{`SmithyToDafny(key)`: `SmithyToDafny(value)``
      builder.append("%1$s".formatted(
          valueTargetShape.accept(
              new AwsSdkToDafnyShapeVisitor(context, "value", writer, filename)
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
      return dataSource;
    }

    @Override
    public String unionShape(UnionShape unionShape) {
      awsSdkToDafnyConversionFunctionWriter.writeConverterForShapeAndMembers(unionShape, context, writer, filename);

      // Import the aws_sdk_to_dafny converter from where the ShapeVisitor was called
      writer.addImport(".aws_sdk_to_dafny",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape));

      // Return a reference to the generated conversion method
      // ex. for shape example.namespace.ExampleShape
      // returns `SmithyToDafny_example_namespace_ExampleShape(input)`
      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape),
          dataSource
      );
    }


  /**
   * Called from the StructureShape converter when the StructureShape has a Polymorph Reference trait.
   * @param shape
   * @return
   */
  protected String referenceStructureShape(StructureShape shape, String dataSourceInsideConversionFunction) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    if (resourceOrService.isResourceShape()) {
      return referenceResourceShape(resourceOrService.asResourceShape().get(),
          dataSourceInsideConversionFunction);
    } else if (resourceOrService.isServiceShape()) {
      return referenceServiceShape(resourceOrService.asServiceShape().get());
    } else {
      throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + shape);
    }
  }

  protected String referenceServiceShape(ServiceShape serviceShape) {
    return "%1$s_client".formatted(SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(
        serviceShape.getId().getNamespace()));
  }

  protected String referenceResourceShape(ResourceShape resourceShape, String dataSourceInsideConversionFunction) {
    // Smithy resource shapes ALWAYS store the underlying Dafny resource in `_impl`.
    // TODO: Typing
    return "%1$s._impl".formatted(dataSourceInsideConversionFunction);
  }

  /**
   * Writes any inline conversions for reference shapes before returning some value.
   * @param shape
   * @param conversionWriter
   * @return
   */
  protected String referenceStructureShapeInlineConversions(StructureShape shape,
      PythonWriter conversionWriter, String dataSourceInsideConversionFunction) {
    ReferenceTrait referenceTrait = shape.expectTrait(ReferenceTrait.class);
    Shape resourceOrService = context.model().expectShape(referenceTrait.getReferentId());

    // Resources do not require any inline conversions, but are still a valid reference shape.
    if (resourceOrService.isResourceShape()) {
      return "";
    } else if (resourceOrService.isServiceShape()) {
      return referenceServiceShapeInlineConversions(resourceOrService.asServiceShape().get(),
          conversionWriter, dataSourceInsideConversionFunction);
    } else {
      throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + shape);
    }
  }

  protected String referenceServiceShapeInlineConversions(ServiceShape serviceShape,
      PythonWriter conversionWriter, String dataSourceInsideConversionFunction) {
    DafnyNameResolver.importDafnyTypeForServiceShape(conversionWriter, serviceShape);
    conversionWriter.addStdlibImport(SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
        serviceShape.getId().getNamespace(), context));
    conversionWriter.addStdlibImport(DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape));

    StringBuilder builder = new StringBuilder();
    // `my_module_client = my_module_internaldafny.MyModuleClient()`
    builder.append("%1$s_client = %2$s.%3$s()\n".formatted(
        SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
        DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape),
        DafnyNameResolver.getDafnyClientTypeForServiceShape(serviceShape)
    ));
    // `my_module_client.ctor__(my_module.smithygenerated.config.smithy_config_to_dafny_config(input._config))`
    builder.append("  %1$s_client.ctor__(%2$s.smithy_config_to_dafny_config(%3$s._config))".formatted(
        SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceShape.getId().getNamespace()),
        SmithyNameResolver.getSmithyGeneratedConfigModulePathForSmithyNamespace(
            serviceShape.getId().getNamespace(), context),
        dataSourceInsideConversionFunction
    ));
    return builder.toString();
  }
}
