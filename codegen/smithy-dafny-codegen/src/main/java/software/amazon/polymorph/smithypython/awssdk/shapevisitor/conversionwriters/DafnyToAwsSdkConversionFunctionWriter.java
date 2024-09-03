// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/** Writes the dafny_to_aws_sdk.py file via the BaseConversionWriter implementation. */
public class DafnyToAwsSdkConversionFunctionWriter
  extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple generations
  static DafnyToAwsSdkConversionFunctionWriter singleton;

  // Instantiate singleton at class-load time
  static {
    singleton = new DafnyToAwsSdkConversionFunctionWriter();
  }

  private DafnyToAwsSdkConversionFunctionWriter() {}

  /**
   * Delegate writing conversion methods for the provided shape and its member shapes
   *
   * @param shape
   * @param context
   * @param writer
   */
  public static void writeConverterForShapeAndMembers(
    Shape shape,
    GenerationContext context,
    PythonWriter writer
  ) {
    singleton.baseWriteConverterForShapeAndMembers(shape, context, writer);
  }

  protected void writeStructureShapeConverter(StructureShape structureShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );
    // Create a new writer.
    // The `writer` on this object points to the location in the code where this converter was
    // called.
    // This new writer to writes the dafny_to_aws_sdk converter function.
    delegator.useFileWriter(
      moduleName + "/dafny_to_aws_sdk.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        // This hardcodes the input parameter name for a conversion function to always be "dafny_input"
        String dataSourceInsideConversionFunction = "dafny_input";

        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getDafnyToAwsSdkFunctionNameForShape(
            structureShape
          ),
          dataSourceInsideConversionFunction,
          () -> {
            // boto3 takes in kwargs
            // Create a dictionary indexed by keys, then cast to kwargs in API call
            conversionWriter.write("output = {}");

            // Recursively dispatch a new ShapeVisitor for each member of the structure
            for (final Entry<
              String,
              MemberShape
            > memberShapeEntry : structureShape.getAllMembers().entrySet()) {
              String memberName = memberShapeEntry.getKey();
              MemberShape memberShape = memberShapeEntry.getValue();
              writeStructureShapeMemberConverter(
                conversionWriter,
                dataSourceInsideConversionFunction,
                memberName,
                memberShape
              );
            }

            conversionWriter.write("return output");
          }
        );
      }
    );
  }

  private void writeStructureShapeMemberConverter(
    PythonWriter conversionWriter,
    String dataSourceInsideConversionFunction,
    String memberName,
    MemberShape memberShape
  ) {
    final Shape targetShape = context
      .model()
      .expectShape(memberShape.getTarget());

    // Optional shapes require an `is_Some` check and their value is accessed via `.value`
    // ex. kms.KeyId in DecryptRequest (optional parameter):
    // if input.KeyId.is_Some:
    //        output["KeyId"] = input.KeyId.value.VerbatimString(False)
    // (`VerbatimString(False)` comes from the DafnyToAwsSdkShapeVisitor)
    if (memberShape.isOptional()) {
      conversionWriter.openBlock(
        "if $L.$L.is_Some:",
        "",
        dataSourceInsideConversionFunction,
        memberName,
        () -> {
          conversionWriter.write(
            "output[\"$L\"] = $L",
            memberName,
            targetShape.accept(
              new DafnyToAwsSdkShapeVisitor(
                context,
                dataSourceInsideConversionFunction +
                "." +
                memberName +
                ".value",
                conversionWriter
              )
            )
          );
        }
      );
      // Required shapes are assigned directly
      // ex. kms.CiphertextBlob in DecryptRequest (required parameter):
      // output["CiphertextBlob"] = bytes(input.CiphertextBlob)
      // (`bytes()` comes from the DafnyToAwsSdkShapeVisitor)
    } else {
      conversionWriter.write(
        "output[\"$L\"] = $L",
        memberName,
        targetShape.accept(
          new DafnyToAwsSdkShapeVisitor(
            context,
            dataSourceInsideConversionFunction + "." + memberName,
            conversionWriter
          )
        )
      );
    }
  }

  /**
   * Writes a function definition to convert a Dafny-modelled union shape into the corresponding
   * Smithy-modelled union shape. The function definition is written into `dafny_to_aws_sdk.py`.
   * This SHOULD only be called once so only one function definition is written.
   *
   * @param unionShape
   */
  public void writeUnionShapeConverter(UnionShape unionShape) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    // Write out common conversion function inside dafny_to_aws_sdk
    delegator.useFileWriter(
      moduleName + "/dafny_to_aws_sdk.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        String dataSourceInsideConversionFunction = "dafny_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getDafnyToAwsSdkFunctionNameForShape(unionShape),
          dataSourceInsideConversionFunction,
          () -> {
            conversionWriter.writeComment(
              "Convert %1$s".formatted(unionShape.getId().getName())
            );

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            // Write out conversion:
            // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
            // if isinstance(input, ExampleUnion_IntegerValue):
            //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
            // elif isinstance(input, ExampleUnion_StringValue):
            //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)
            for (final MemberShape memberShape : unionShape
              .getAllMembers()
              .values()) {
              final Shape targetShape = context
                .model()
                .expectShape(memberShape.getTarget());
              conversionWriter.write(
                """
                $L isinstance($L, $L):
                    $L_union_value = {"$L": $L}""",
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                DafnyNameResolver.getDafnyTypeForUnion(unionShape, memberShape),
                unionShape.getId().getName(),
                memberShape.getMemberName(),
                targetShape.accept(
                  new DafnyToAwsSdkShapeVisitor(
                    context,
                    dataSourceInsideConversionFunction +
                    "." +
                    memberShape.getMemberName(),
                    conversionWriter
                  )
                )
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForUnion(
                conversionWriter,
                unionShape,
                memberShape,
                context
              );
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write(
              """
              else:
                  raise ValueError("No recognized union value in union type: " + str($L))
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
      }
    );
  }

  /**
   * @param stringShapeWithEnumTrait
   */
  public void writeStringEnumShapeConverter(
    StringShape stringShapeWithEnumTrait
  ) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    // Write out common conversion function inside dafny_to_aws_sdk
    delegator.useFileWriter(
      moduleName + "/dafny_to_aws_sdk.py",
      "",
      conversionWriter -> {
        // Within the conversion function, the dataSource becomes the function's input
        String dataSourceInsideConversionFunction = "dafny_input";

        // ex. shape: simple.union.ExampleUnion
        // Writes `def DafnyToSmithy_simple_union_ExampleUnion(input):`
        //   and wraps inner code inside function definition
        conversionWriter.openBlock(
          "def $L($L):",
          "",
          AwsSdkNameResolver.getDafnyToAwsSdkFunctionNameForShape(
            stringShapeWithEnumTrait
          ),
          dataSourceInsideConversionFunction,
          () -> {
            conversionWriter.writeComment(
              "Convert %1$s".formatted(
                  stringShapeWithEnumTrait.getId().getName()
                )
            );

            // First union value opens a new `if` block; others do not need to and write `elif`
            boolean shouldOpenNewIfBlock = true;
            // Write out conversion:
            // ex. if ExampleUnion can take on either of (IntegerValue, StringValue), write:
            // if isinstance(input, ExampleUnion_IntegerValue):
            //   ExampleUnion_union_value = ExampleUnionIntegerValue(input.IntegerValue)
            // elif isinstance(input, ExampleUnion_StringValue):
            //   ExampleUnion_union_value = ExampleUnionStringValue(input.StringValue)

            for (final EnumDefinition enumDefinition : stringShapeWithEnumTrait
              .getTrait(EnumTrait.class)
              .get()
              .getValues()) {
              String value = enumDefinition.getValue();
              conversionWriter.write(
                """
                $L isinstance($L, $L):
                    return "$L"
                """,
                // If we need a new `if` block, open one; otherwise, expand on existing one
                // with `elif`
                shouldOpenNewIfBlock ? "if" : "elif",
                dataSourceInsideConversionFunction,
                DafnyNameResolver.getDafnyTypeForStringShapeWithEnumTrait(
                  stringShapeWithEnumTrait,
                  value
                ),
                value
              );
              shouldOpenNewIfBlock = false;

              DafnyNameResolver.importDafnyTypeForStringShapeWithEnumTrait(
                conversionWriter,
                stringShapeWithEnumTrait,
                value,
                context
              );
            }

            // Write case to handle if union member does not match any of the above cases
            conversionWriter.write(
              """
              else:
                  raise ValueError("No recognized enum value in enum type: " + $L)
              """,
              dataSourceInsideConversionFunction
            );
          }
        );
      }
    );
  }
}
