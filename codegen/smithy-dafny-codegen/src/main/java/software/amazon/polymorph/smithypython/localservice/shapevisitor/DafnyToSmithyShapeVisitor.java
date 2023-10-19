package software.amazon.polymorph.smithypython.localservice.shapevisitor;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
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
public class DafnyToSmithyShapeVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private String dataSource;
    private final PythonWriter writer;
    private final String filename;
    // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
    // have already generated a conversion function, so we only write each conversion function once.
    private static final Set<Shape> generatedShapes = new HashSet<>();

    /**
     * @param context     The generation context.
     * @param dataSource  The in-code location of the data to provide an output of
     *                    ({@code output.foo}, {@code entry}, etc.)
     * @param writer      The PythonWriter being used
     * @param filename    Filename where code is being generated.
     *                    This is used to avoid generating an import for the current file.
     */
    public DafnyToSmithyShapeVisitor(
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
      return dataSource;
    }

    @Override
    public String structureShape(StructureShape shape) {
      if (!generatedShapes.contains(shape)) {
        generatedShapes.add(shape);
        writeStructureShapeConverter(shape);
      }

      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(shape),
          dataSource
      );
    }

    private void writeStructureShapeConverter(StructureShape shape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();
      // Create a new writer.
      // The `writer` on this object points to the location in the code where this converter was called.
      // This new writer to writes the dafny_to_smithy converter function.
      delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {
        conversionWriter.write(
        """
        def $L(input):
            return $L
        """,
            SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(shape),
            getStructureShapeConverterBody(shape, conversionWriter)
        );
      });
    }

    private String getStructureShapeConverterBody(StructureShape shape, PythonWriter conversionWriter) {
      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      // Reference shapes have different logic
      if (shape.hasTrait(ReferenceTrait.class)) {
        return referenceStructureShape(shape, dataSourceInsideConversionFunction);
      }

      SmithyNameResolver.importSmithyGeneratedTypeForShape(conversionWriter, shape, context);
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
        builder.append("\n        %1$s=%2$s,".formatted(
            CaseUtils.toSnakeCase(memberName),
            targetShape.accept(
                new DafnyToSmithyShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction + "." + memberName
                        + (memberShape.isOptional() ? ".UnwrapOr(None)" : ""),
                    writer,
                    filename)
            )
          ));
      }
      // Close structure
      return builder.append("\n    )").toString();
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
              new DafnyToSmithyShapeVisitor(context, "list_element", writer, filename)
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
            new DafnyToSmithyShapeVisitor(context, "key", writer, filename)
        )
    ));

    // Write converted map values into the map:
    // `{`DafnyToSmithy(key)`: `DafnyToSmithy(value)``
    builder.append("%1$s".formatted(
        valueTargetShape.accept(
            new DafnyToSmithyShapeVisitor(context, "value", writer, filename)
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
      if (!generatedShapes.contains(unionShape)) {
        generatedShapes.add(unionShape);
        writeUnionShapeConverter(unionShape);
      }

      return "%1$s(%2$s)".formatted(
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(unionShape),
          dataSource
      );
    }

  /**
   * Writes a function definition to convert a Dafny-modelled union shape
   *   into the corresponding Smithy-modelled union shape.
   * The function definition is written into `dafny_to_smithy.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  public void writeUnionShapeConverter(UnionShape unionShape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      // Write out common conversion function inside dafny_to_smithy
      delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {

        // Within the conversion function, the dataSource becomes the function's input
        String dataSourceInsideConversionFunction = "input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
            "def $L($L):",
            "",
            SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(unionShape),
            dataSourceInsideConversionFunction,
            () -> {
              conversionWriter.writeComment("Convert %1$s".formatted(
                  unionShape.getId().getName()
              ));

              // First union value opens a new `if` block; others do not need to and write `elif`
              boolean shouldOpenNewIfBlock = true;
              // Write out conversion:
              // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
              // if isinstance(input, ExampleUnion_IntegerValue):
              //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
              // elif isinstance(input, ExampleUnion_StringValue):
              //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)
              for (MemberShape memberShape : unionShape.getAllMembers().values()) {
                conversionWriter.write(
                    """
                    $L isinstance($L, $L):
                        $L_union_value = $L($L.$L)""",
                    // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                    shouldOpenNewIfBlock ? "if" : "elif",
                    dataSourceInsideConversionFunction,
                    DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                    unionShape.getId().getName(),
                    SmithyNameResolver.getSmithyGeneratedTypeForUnion(unionShape, memberShape),
                    dataSourceInsideConversionFunction,
                    memberShape.getMemberName()
                );
                shouldOpenNewIfBlock = false;

                DafnyNameResolver.importDafnyTypeForUnion(conversionWriter, unionShape, memberShape);
                SmithyNameResolver.importSmithyGeneratedTypeForUnion(conversionWriter, context, unionShape, memberShape);
              }

              // Write case to handle if union member does not match any of the above cases
              conversionWriter.write("""
                  else:
                      raise ValueError("No recognized union value in union type: " + $L)
                  """,
                  dataSourceInsideConversionFunction
              );

              // Write return value:
              // `return ExampleUnion_union_value`
              conversionWriter.write(
                  """
                  return $L_union_value
                  """,
                  unionShape.getId().getName()
              );
            }
        );
      });
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
        return referenceResourceShape(resourceOrService.asResourceShape().get(), dataSourceInsideConversionFunction);
      } else if (resourceOrService.isServiceShape()) {
        return referenceServiceShape(resourceOrService.asServiceShape().get(), dataSourceInsideConversionFunction);
      } else {
        throw new UnsupportedOperationException("Unknown referenceStructureShape type: " + shape);
      }
    }

    protected String referenceResourceShape(ResourceShape resourceShape, String dataSourceInsideConversionFunction) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();
      delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {
        conversionWriter.addImport(
            SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
                resourceShape.getId().getNamespace(), context
            ) + ".references",
            resourceShape.getId().getName());
      });

      return "%1$s(_impl=%2$s)".formatted(resourceShape.getId().getName(), dataSourceInsideConversionFunction);
    }

    protected String referenceServiceShape(ServiceShape serviceShape, String dataSourceInsideConversionFunction) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();
      delegator.useFileWriter(moduleName + "/dafny_to_smithy.py", "", conversionWriter -> {
        conversionWriter.addImport(
            SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
                serviceShape.getId().getNamespace(), context
            ) + ".client",
            serviceShape.getId().getName());
          });

      return "%1$s(%2$s)".formatted(serviceShape.getId().getName(), dataSourceInsideConversionFunction);
    }
}
