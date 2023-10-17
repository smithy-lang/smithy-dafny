package software.amazon.polymorph.smithypython.customize;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.Constants.GenerationType;
import software.amazon.polymorph.smithypython.extensions.DafnyPythonSettings;
import software.amazon.polymorph.smithypython.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.Utils;
import software.amazon.polymorph.smithypython.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file.
 * The shim wraps the client.py implementation (which itself wraps the underlying Dafny implementation).
 * Other Dafny-generated Python code may use the shim to interact with this project's Dafny implementation
 *   through the Polymorph wrapper.
 */
public class DafnyToAwsSdkFileWriter implements CustomFileWriter {

  // Store the set of shapes for which this ShapeVisitor (and ShapeVisitors that extend this)
  // have already generated a conversion function, so we only write each conversion function once.
  private static final Set<Shape> generatedShapes = new HashSet<>();
  static final List<Shape> shapesToGenerate = new ArrayList<>();
  static boolean generating = false;

  public static void writeShapeConversionFunction(Shape shape, GenerationContext context,
      PythonWriter writer, String filename) {
    if (!generatedShapes.contains(shape) && !shapesToGenerate.contains(shape)) {
      shapesToGenerate.add(shape);
    }

    while (!generating && !shapesToGenerate.isEmpty()) {
      generating = true;

      Shape toGenerate = shapesToGenerate.remove(0);
      generatedShapes.add(toGenerate);

      if (toGenerate.isStructureShape()) {
        writeStructureShapeConversionFunction(toGenerate.asStructureShape().get(), context, writer, filename);
      } else if (toGenerate.isUnionShape()) {
        writeUnionShapeConverter(toGenerate.asUnionShape().get(), context, writer, filename);
      }

      generating = false;
    }

  }

  private static void writeStructureShapeConversionFunction(StructureShape structureShape, GenerationContext context,
      PythonWriter writer, String filename) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();
    // Create a new writer.
    // The `writer` on this object points to the location in the code where this converter was called.
    // This new writer to writes the dafny_to_aws_sdk converter function.
    delegator.useFileWriter(moduleName + "/dafny_to_aws_sdk.py", "", conversionWriter -> {
      conversionWriter.openBlock(
          "def $L(input):",
          "",
          SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(structureShape),
          () -> {
            writeStructureShapeConverterBody(structureShape, conversionWriter, context, writer, filename);
          }
      );
    });

  }

  private static void writeStructureShapeConverterBody(StructureShape shape, PythonWriter conversionWriter, GenerationContext context,
      PythonWriter writer, String filename) {
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

  /**
   * Writes a function definition to convert a Dafny-modelled union shape
   *   into the corresponding Smithy-modelled union shape.
   * The function definition is written into `dafny_to_aws_sdk.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  public static void writeUnionShapeConverter(UnionShape unionShape, GenerationContext context, PythonWriter writer, String filename) {
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
              final Shape targetShape = context.model().expectShape(memberShape.getTarget());
              conversionWriter.write(
                  """
                  $L isinstance($L, $L):
                      $L_union_value = {"$L": $L}""",
                  // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                  shouldOpenNewIfBlock ? "if" : "elif",
                  dataSourceInsideConversionFunction,
                  DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                  unionShape.getId().getName(),

                  memberShape.getMemberName(),
                  targetShape.accept(new DafnyToAwsSdkShapeVisitor(
                      context,
                      dataSourceInsideConversionFunction + "." + memberShape.getMemberName(),
                      writer,
                      filename
                  ))
              );
              shouldOpenNewIfBlock = false;

              AwsSdkNameResolver.importDafnyTypeForUnion(conversionWriter, unionShape, memberShape);
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

}
