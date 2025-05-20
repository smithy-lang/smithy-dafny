// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.shapevisitor.conversionwriters;

import java.util.Map.Entry;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkFormatShapeVisitor;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.conversionwriter.BaseConversionWriter;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/** Writes the aws_sdk_format_converter.py file via the BaseConversionWriter implementation. */
public class AwsSdkFormatConversionFunctionWriter
  extends BaseConversionWriter {

  // Use a singleton to preserve generatedShapes through multiple generations
  static AwsSdkFormatConversionFunctionWriter singleton;

  // Instantiate singleton at class-load time
  static {
    singleton = new AwsSdkFormatConversionFunctionWriter();
  }

  private AwsSdkFormatConversionFunctionWriter() {}

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

    delegator.useFileWriter(
      moduleName + "/aws_sdk_format_converter.py",
      "",
      conversionWriter -> {

        conversionWriter.openBlock(
          "def $L($L, $L, $L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(
            structureShape
          ),
          "this_structure",
          "item_handler",
          "condition_handler",
          () -> {
            // deepcopy the output to avoid modifying the original structure
            conversionWriter.addStdlibImport("copy", "deepcopy");
            conversionWriter.write("transformed_output = deepcopy(this_structure)");

            String dataSourceInsideConversionFunction = "this_structure";
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

            conversionWriter.write("return transformed_output");
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

    // If the shape is a condition "expression string",
    // call the condition_handler function to handle converting it.
    if (targetShape.getId().equals(ShapeId.from("com.amazonaws.dynamodb#ConditionExpression"))
    || targetShape.getId().equals(ShapeId.from("com.amazonaws.dynamodb#KeyExpression"))) {
      conversionWriter.openBlock(
        "if \"$L\" in $L:",
        "",
        memberName,
        dataSourceInsideConversionFunction,
        () -> {
          conversionWriter.write("""
            condition_expression, attribute_names, attribute_values = condition_handler("$L", $L)
            transformed_output["$L"] = condition_expression
            if len(attribute_names) > 0:
              $L.setdefault("ExpressionAttributeNames", {}).update(attribute_names)
            if len(attribute_values) > 0:
              $L.setdefault("ExpressionAttributeValues", {}).update(attribute_values)
          """,
          memberName,
          dataSourceInsideConversionFunction,
          memberName,
          dataSourceInsideConversionFunction,
          dataSourceInsideConversionFunction
          );
        }
      );
      
    }

    // For non-"expression string" structure shapes, recurse into the structure
    else if (memberShape.isOptional()) {
      conversionWriter.openBlock(
        "if \"$L\" in $L:",
        "",
        memberName,
        dataSourceInsideConversionFunction,
        () -> {
          conversionWriter.write(
            "transformed_output[\"$L\"] = $L",
            memberName,
            targetShape.accept(
              new AwsSdkFormatShapeVisitor(
                context,
                dataSourceInsideConversionFunction +
                "[\"" +
                memberName +
                "\"]",
                conversionWriter
              )
            )
          );
        }
      );
    } else {
      conversionWriter.write(
            "transformed_output[\"$L\"] = $L",
            memberName,
            targetShape.accept(
              new AwsSdkFormatShapeVisitor(
                context,
                dataSourceInsideConversionFunction +
                "[\"" +
                memberName +
                "\"]",
                conversionWriter
              )
            )
          );
    }
  }

  /**
   * There doesn't seem to be any union shapes that require recursive conversions,
   * but the interface requires this method.
   * @param unionShape
   */
  public void writeUnionShapeConverter(UnionShape unionShape) {
    throw new UnsupportedOperationException("No boto3 DynamoDB union shapes require recursive conversions");
  }

  /**
   * Enums don't seem to require any conversion.
   * Always return the input value.
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

    delegator.useFileWriter(
      moduleName + "/aws_sdk_format_converter.py",
      "",
      conversionWriter -> {
        String dataSourceInsideConversionFunction = "this_structure";

        conversionWriter.openBlock(
          "def $L($L, $L, $L):",
          "",
          AwsSdkNameResolver.getAwsSdkToDafnyFunctionNameForShape(
            stringShapeWithEnumTrait
          ),
          "this_structure",
          "item_handler",
          "condition_handler",
          () -> {
            conversionWriter.writeComment(
              "Always return input enum"
            );

            conversionWriter.write("return $L", dataSourceInsideConversionFunction);

          }
        );
      }
    );
  }
}
