package software.amazon.polymorph.smithypython.shapevisitor;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
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
import software.amazon.smithy.utils.CaseUtils;

/**
 * ShapeVisitor that should be dispatched from a shape
 * to generate code that maps a Dafny shape's internal attributes
 * to the corresponding Smithy shape's internal attributes.
 *
 * This generates code in a `dafny_to_aws_sdk.py` file.
 * The generated code consists of methods that convert from a Dafny-modelled shape
 *   to a Smithy-modelled shape.
 * Code that requires these conversions will call out to this file.
 */
public class DafnyToAwsSdkShapeVisitor extends ShapeVisitor.Default<String> {
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
    public DafnyToAwsSdkShapeVisitor(
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
      return "bytes(%1$s)".formatted(dataSource);
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
      // This new writer to writes the dafny_to_aws_sdk converter function.
      delegator.useFileWriter(moduleName + "/dafny_to_aws_sdk.py", "", conversionWriter -> {
        conversionWriter.openBlock(
        "def $L(input):",
        "",
        SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(shape),
            () -> {
          writeStructureShapeConverterBody(shape, conversionWriter);
        }
        );
      });
    }

    private void writeStructureShapeConverterBody(StructureShape shape, PythonWriter conversionWriter) {
      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      conversionWriter.write("output = {}");

      System.out.println(shape.getAllMembers());

      // Recursively dispatch a new ShapeVisitor for each member of the structure
      for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
        String memberName = memberShapeEntry.getKey();
        MemberShape memberShape = memberShapeEntry.getValue();
        final Shape targetShape = context.model().expectShape(memberShape.getTarget());

        if (memberShape.isOptional()) {
          conversionWriter.openBlock("if $L.$L.is_Some:",
              "",
              dataSourceInsideConversionFunction,
              memberName,
              () -> {
                conversionWriter.write("output[\"$L\"] = $L",
                    memberName,
                    targetShape.accept(new DafnyToAwsSdkShapeVisitor(
                        context,
                        dataSourceInsideConversionFunction + "." + memberName + ".value",
                        writer,
                        filename
                    )));
              });
        } else {
          conversionWriter.write("output[\"$L\"] = $L",
              memberName,
              targetShape.accept(new DafnyToAwsSdkShapeVisitor(
                  context,
                  dataSourceInsideConversionFunction + "." + memberName,
                  writer,
                  filename
              )));
        }
      }

      conversionWriter.write("return output");
    }

    @Override
    // TODO
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
              new DafnyToAwsSdkShapeVisitor(context, "list_element", writer, filename)
          )));

      // Close structure:
      // `[list_element for list_element in `DafnyToSmithy(targetShape)`]`
      return builder.append(" for list_element in %1$s]".formatted(dataSource)).toString();
    }

  @Override
  // TODO
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
            new DafnyToAwsSdkShapeVisitor(context, "key", writer, filename)
        )
    ));

    // Write converted map values into the map:
    // `{`DafnyToSmithy(key)`: `DafnyToSmithy(value)``
    builder.append("%1$s".formatted(
        valueTargetShape.accept(
            new DafnyToAwsSdkShapeVisitor(context, "value", writer, filename)
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
      return dataSource + ".VerbatimString(False)";
    }

    /*
    def DafnyToSmithy_com_amazonaws_kms_DecryptRequest(input):
    output = {}
    output["CiphertextBlob"] = bytes(input.CiphertextBlob)
    if input.EncryptionContext.UnwrapOr(None) is not None:
        output["EncryptionContext"] = {key: value for (key, value) in input.EncryptionContext.value.items}
    if input.GrantTokens.UnwrapOr(None) is not None:
        output["GrantTokens"] = [list_element for list_element in input.GrantTokens.UnwrapOr(None)]
    if input.KeyId.UnwrapOr(None) is not None:
        output["KeyId"] = input.KeyId.UnwrapOr(None).VerbatimString(False)
    if input.EncryptionAlgorithm.UnwrapOr(None) is not None:
        output["EncryptionAlgorithm"] = input.EncryptionAlgorithm.UnwrapOr(None)
    return output
     */

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
   * The function definition is written into `dafny_to_aws_sdk.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  public void writeUnionShapeConverter(UnionShape unionShape) {
      WriterDelegator<PythonWriter> delegator = context.writerDelegator();
      String moduleName = context.settings().getModuleName();

      // Write out common conversion function inside dafny_to_aws_sdk
      delegator.useFileWriter(moduleName + "/dafny_to_aws_sdk.py", "", conversionWriter -> {

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
      delegator.useFileWriter(moduleName + "/dafny_to_aws_sdk.py", "", conversionWriter -> {
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
      delegator.useFileWriter(moduleName + "/dafny_to_aws_sdk.py", "", conversionWriter -> {
        conversionWriter.addImport(
            SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
                serviceShape.getId().getNamespace(), context
            ) + ".client",
            serviceShape.getId().getName());
          });

      return "%1$s(%2$s)".formatted(serviceShape.getId().getName(), dataSourceInsideConversionFunction);
    }
}
