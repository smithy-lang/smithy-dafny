// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.customize;

import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkFormatShapeVisitor;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Write a boto3_conversions.py file for AWS SDKs.
 * The generated file contains a InternalBoto3DynamoDBFormatConverter class
 * with an operation for each operation on a DynamoDB client.
 * Each operation on this class takes in a boto3 dictionary shape
 * from either a Client (boto3.client("dynamodb"))
 * or a Resource (boto3.resource("dynamodb"), maybe with .Table())
 * and converts it to the other format.
 * Creating an instance of this class requires two manually-written functions:
 * - item_handler: Method that converts any `AttributeValue`s in the input to the other format.
 * - expression_handler: Method that converts "expressions" in the input to the other format.
 *    This may be either `KeyExpression` or `ConditionExpression`.
 */
public class Boto3DynamoDBFormatConverterWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    // Only generate the boto3_conversions.py file for DynamoDB.
    if (
      !serviceShape
        .getId()
        .equals(
          ShapeId.fromParts("com.amazonaws.dynamodb", "DynamoDB_20120810")
        )
    ) {
      return;
    }
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    codegenContext
      .writerDelegator()
      .useFileWriter(moduleName + "/boto3_conversions.py", "", writer -> {
        writer.write(
          """
          class InternalBoto3DynamoDBFormatConverter:
              def __init__(self, item_handler, condition_handler):
                  self._item_handler = item_handler
                  self._condition_handler = condition_handler

              ${C|}

              """,
          writer.consumer(w ->
            generateOperationsBlock(codegenContext, serviceShape, w)
          )
        );
      });
  }

  /**
   * Generate shim methods for all operations in the SDK service shape.
   * Each method will take in a
   * Dafny input into a dictionary whose keys are boto3 API request parameters, call the boto3
   * client with the request dictionary mapped to its kwargs representation, receive a boto3
   * response, convert the response into its corresponding Dafny type, and return the Dafny type.
   *
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateOperationsBlock(
    GenerationContext codegenContext,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      writer.openBlock(
        "def $L(self, boto3_input) -> dict:",
        "",
        inputShape.getName(),
        () -> {
          Shape targetShapeInput = codegenContext
            .model()
            .expectShape(inputShape);
          String input = targetShapeInput.accept(
            new AwsSdkFormatShapeVisitor(codegenContext, "boto3_input", writer)
          );
          writer.write(
            """
            original_request = boto3_input
            item_handler = self._item_handler
            condition_handler = self._condition_handler
            return $L
            """,
            input
          );
        }
      );

      writer.openBlock(
        "def $L(self, boto3_input) -> dict:",
        "",
        outputShape.getName(),
        () -> {
          Shape targetShapeOutput = codegenContext
            .model()
            .expectShape(outputShape);
          String output = targetShapeOutput.accept(
            new AwsSdkFormatShapeVisitor(codegenContext, "boto3_input", writer)
          );
          writer.addStdlibImport("copy", "deepcopy");
          writer.write(
            """
            original_request = deepcopy(boto3_input)
            item_handler = self._item_handler
            condition_handler = self._condition_handler
            return $L
            """,
            output
          );
        }
      );
    }
  }
}
