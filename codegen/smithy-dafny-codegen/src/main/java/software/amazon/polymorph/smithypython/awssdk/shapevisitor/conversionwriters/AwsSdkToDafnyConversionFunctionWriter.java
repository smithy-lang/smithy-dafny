package software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriters.BaseConversionWriter;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file.
 * The shim wraps the client.py implementation (which itself wraps the underlying Dafny implementation).
 * Other Dafny-generated Python code may use the shim to interact with this project's Dafny implementation
 *   through the Polymorph wrapper.
 */
public class AwsSdkToDafnyConversionFunctionWriter extends BaseConversionWriter {

  static AwsSdkToDafnyConversionFunctionWriter singleton = null;

  private AwsSdkToDafnyConversionFunctionWriter() { }

  public static AwsSdkToDafnyConversionFunctionWriter getWriter() {
    if (singleton == null) {
      singleton = new AwsSdkToDafnyConversionFunctionWriter();
    }
    return singleton;
  }

  public void writeStructureShapeConverter(StructureShape structureShape, GenerationContext context,
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
    AwsSdkNameResolver.importDafnyTypeForAwsSdkShape(conversionWriter, shape.getId(), context);
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
  public void writeUnionShapeConverter(UnionShape unionShape, GenerationContext context,
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
