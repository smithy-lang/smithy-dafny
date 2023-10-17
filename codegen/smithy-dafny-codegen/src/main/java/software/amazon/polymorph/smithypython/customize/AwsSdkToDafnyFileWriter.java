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
import software.amazon.polymorph.traits.ReferenceTrait;
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
public class AwsSdkToDafnyFileWriter implements CustomFileWriter {

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

    delegator.useFileWriter(moduleName + "/aws_sdk_to_dafny.py", "", conversionWriter -> {
      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      conversionWriter.write(
          """
          def $L($L):
            return $L
          """,
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(structureShape),
          dataSourceInsideConversionFunction,
          getStructureShapeConverterBody(structureShape, conversionWriter, dataSourceInsideConversionFunction, context, writer, filename)
      );
    });

  }

  public static String getStructureShapeConverterBody(StructureShape shape, PythonWriter conversionWriter, String dataSourceInsideConversionFunction,
      GenerationContext context,
      PythonWriter writer, String filename) {
    AwsSdkNameResolver.importDafnyTypeForShape(conversionWriter, shape.getId(), context);
    StringBuilder builder = new StringBuilder();
    // Open Dafny structure shape
    // e.g.
    // DafnyStructureName(...
    builder.append("%1$s(".formatted(AwsSdkNameResolver.getDafnyTypeForShape(shape)));
    // Recursively dispatch a new ShapeVisitor for each member of the structure
    for (Entry<String, MemberShape> memberShapeEntry : shape.getAllMembers().entrySet()) {
      String memberName = memberShapeEntry.getKey();
      MemberShape memberShape = memberShapeEntry.getValue();
      final Shape targetShape = context.model().expectShape(memberShape.getTarget());

      // Adds `DafnyStructureMember=smithy_structure_member(...)`
      // e.g.
      // DafnyStructureName(DafnyStructureMember=smithy_structure_member(...), ...)
      // The nature of the `smithy_structure_member` conversion depends on the properties of the shape,
      //   as described below
      builder.append("%1$s=".formatted(memberName));

//      // If this is a localService config shape, defer conversion to the config ShapeVisitor
//      if (SmithyNameResolver.getLocalServiceConfigShapes(context).contains(targetShape.getId())) {
//        builder.append("%1$s,\n".formatted(
//            targetShape.accept(
//                new AwsSdkToDafnyShapeVisitor(
//                    context,
//                    dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
//                    writer,
//                    filename
//                )
//            )
//        ));
//      }

      /*
      def SmithyToDafny_com_amazonaws_kms_DecryptResponse(input):
  return DafnyDecryptResponse(KeyId=Option_Some(Seq(input["KeyId"])),
Plaintext=Option_Some(Seq(input["Plaintext"])),
EncryptionAlgorithm=Option_Some(Seq(input["EncryptionAlgorithm"]))
)
       */

      // If this shape is optional, write conversion logic to detect and possibly pass
      //   an empty optional at runtime
      if (memberShape.isOptional()) {
        conversionWriter.addStdlibImport("Wrappers", "Option_Some");
        conversionWriter.addStdlibImport("Wrappers", "Option_None");
        builder.append("Option_Some(%1$s) if \"%2$s\" in %3$s.keys() else Option_None(),\n".formatted(
            targetShape.accept(
                new AwsSdkToDafnyShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
                    writer,
                    filename
                )
            ),
            memberName,
            dataSourceInsideConversionFunction
            ));
      }

      // If this shape is required, pass in the shape for conversion without any optional-checking
      else {
        builder.append("%1$s,\n".formatted(
            targetShape.accept(
                new AwsSdkToDafnyShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction + "[\"" + memberName + "\"]",
                    writer,
                    filename
                )
            )
        ));
      }
    }
    // Close structure
    return builder.append(")").toString();
  }

  /**
   * Writes a function definition to convert a Smithy-modelled union shape
   *   into the corresponding Dafny-modelled union shape.
   * The function definition is written into `aws_sdk_to_dafny.py`.
   * This SHOULD only be called once so only one function definition is written.
   * @param unionShape
   */
  public static void writeUnionShapeConverter(UnionShape unionShape, GenerationContext context,
      PythonWriter writer, String filename) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    delegator.useFileWriter(moduleName + "/aws_sdk_to_dafny.py", "", conversionWriter -> {

      // Within the conversion function, the dataSource becomes the function's input
      // This hardcodes the input parameter name for a conversion function to always be "input"
      String dataSourceInsideConversionFunction = "input";

      // ex. shape: simple.union.ExampleUnion
      // Writes `def SmithyToDafny_simple_union_ExampleUnion(input):`
      //   and wraps inner code inside function definition
      conversionWriter.openBlock(
          "def $L($L):",
          "",
          SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(unionShape),
          dataSourceInsideConversionFunction,
          () -> {

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            for (MemberShape memberShape : unionShape.getAllMembers().values()) {
              final Shape targetShape = context.model().expectShape(memberShape.getTarget());
              // Write out conversion:
              // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
              // if isinstance(input, ExampleUnion.IntegerValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              // elif isinstance(input, ExampleUnion.StringValue):
              //   example_union_union_value = DafnyExampleUnionIntegerValue(input.member.value)
              conversionWriter.write("""
                        $L "$L" in $L.keys():
                            $L_union_value = $L($L)""",
                  // If we need a new `if` block, open one; otherwise, expand on existing one with `elif`
                  shouldOpenNewIfBlock ? "if" : "elif",
                  memberShape.getMemberName(),
                  dataSourceInsideConversionFunction,

                  unionShape.getId().getName(),
                  DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                  targetShape.accept(
                      new AwsSdkToDafnyShapeVisitor(
                          context,
                          dataSourceInsideConversionFunction + "[\"" + memberShape.getMemberName() + "\"]",
                          writer,
                          filename
                      )
                  )
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

            // Return the result of the union conversion
            // `return example_union_union_value`
            conversionWriter.write("return %1$s_union_value".formatted(unionShape.getId().getName()));
          });
    });
  }

}
