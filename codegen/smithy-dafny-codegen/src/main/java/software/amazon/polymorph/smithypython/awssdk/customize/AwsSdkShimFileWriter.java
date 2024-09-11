// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.customize;

import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file for AWS SDKs. The shim wraps boto3 calls. Its inputs are Dafny-modeled
 * requests; its outputs are Dafny-modelled responses. Internally, the shim will convert the
 * Dafny-modelled requests to dictionaries passed to boto3 via kwargs, call boto3 with the request
 * return the Dafny-modelled response. Other Dafny-generated Python code will use the shim to call
 * AWS services (e.g. KMS, DDB).
 */
public class AwsSdkShimFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String typesModulePrelude =
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        serviceShape.getId(),
        codegenContext
      );
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/shim.py",
        "",
        writer -> {
          writer.write(
            """
            import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers
            from botocore.exceptions import ClientError
            import $L

            def _sdk_error_to_dafny_error(e: ClientError):
                ""\"
                Converts the provided native Smithy-modelled error
                into the corresponding Dafny error.
                ""\"
                ${C|}

            class $L:
                def __init__(self, _impl, _region):
                    self._impl = _impl
                    self._region = _region

                ${C|}

                """,
            typesModulePrelude,
            writer.consumer(w ->
              generateAwsSdkErrorToDafnyErrorBlock(
                codegenContext,
                serviceShape,
                w
              )
            ),
            AwsSdkNameResolver.shimNameForService(serviceShape),
            writer.consumer(w ->
              generateOperationsBlock(codegenContext, serviceShape, w)
            )
          );
        }
      );
  }

  /**
   * Generate the method body for the `_sdk_error_to_dafny_error` method. This writes out a block to
   * convert a boto3 ClientError modelled in JSON into a Dafny-modelled error
   *
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateAwsSdkErrorToDafnyErrorBlock(
    GenerationContext codegenContext,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    // Get modelled error converters for this service
    TreeSet<ShapeId> errorShapeSet = new TreeSet<ShapeId>(
      codegenContext
        .model()
        .getStructureShapesWithTrait(ErrorTrait.class)
        .stream()
        .filter(structureShape ->
          structureShape
            .getId()
            .getNamespace()
            .equals(codegenContext.settings().getService().getNamespace())
        )
        .map(Shape::getId)
        .collect(Collectors.toSet())
    );

    // First error case opens a new `if` block; others do not need to, and write `elif`
    boolean hasOpenedIfBlock = false;

    for (ShapeId errorShapeId : errorShapeSet) {
      // ex. for KMS.InvalidImportTokenException:
      // if e.response['Error']['Code'] == 'InvalidImportTokenException':
      //        return
      // software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidImportTokenException(message=e.response['Error']['Code'])
      Shape errorShape = codegenContext.model().expectShape(errorShapeId);
      writer.openBlock(
        "$L e.response['Error']['Code'] == '$L':",
        "",
        hasOpenedIfBlock ? "elif" : "if",
        errorShapeId.getName(),
        () -> {
          writer.write(
            "return %1$s".formatted(
                errorShape.accept(
                  new AwsSdkToDafnyShapeVisitor(
                    codegenContext,
                    "e.response",
                    writer
                  )
                )
              )
          );
        }
      );
      hasOpenedIfBlock = true;
    }

    if (hasOpenedIfBlock) {
      // If `hasOpenedIfBlock` is false, then codegen never wrote any errors,
      // and this function should only cast to Opaque errors
      writer.write(
        """
        return $L.Error_Opaque(obj=e)
        """,
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
          serviceShape.getId(),
          codegenContext
        )
      );
    } else {
      // If `hasOpenedIfBlock` is true, then codegen wrote at least one error,
      // and this function should only cast to Opaque error via `else`
      writer.write(
        """
        else:
            return $L.Error_Opaque(obj=e)
        """,
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
          serviceShape.getId(),
          codegenContext
        )
      );
    }
  }

  /**
   * Generate shim methods for all operations in the SDK service shape. Each method will take in a
   * Dafny type as input and return a Dafny type as output. Internally, each method will convert the
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

      // Import input/output shape types
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        inputShape,
        codegenContext
      );
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        outputShape,
        codegenContext
      );

      // No 'native' type to import; native AWS SDK types are modelled in dictionaries

      // Write the Shim operation block.
      // This takes in a Dafny input and returns a Dafny output.
      // This operation will:
      //  1) Convert the Dafny input to a dictionary with keys as AWS SDK API input names;
      //  2) Call boto3 client with the input transformed to kwargs; and
      //  3) Convert the Smithy output to the Dafny type.
      writer.openBlock(
        "def $L(self, $L) -> $L:",
        "",
        operationShape.getId().getName(),
        // Do not generate an `input` parameter if the operation does not take in an input
        SmithyNameResolver.isUnitShape(inputShape)
          ? ""
          : "input: " + DafnyNameResolver.getDafnyTypeForShape(inputShape),
        // Return `None` type if the operation does not return an output
        SmithyNameResolver.isUnitShape(outputShape)
          ? "None"
          : DafnyNameResolver.getDafnyTypeForShape(outputShape),
        () -> {
          Shape targetShapeInput = codegenContext
            .model()
            .expectShape(operationShape.getInputShape());
          // Generate code that converts the input from the Dafny type to the corresponding Smithy
          // type
          // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled
          // output.
          // If this is a type that allows for self-recursion (unions or sets: can contain
          // themselves as a member),
          //   this will delegate to DafnyToAwsSdkConversionFunctionWriter
          String input = targetShapeInput.accept(
            new DafnyToAwsSdkShapeVisitor(codegenContext, "input", writer)
          );
          writer.addImport(".", "dafny_to_aws_sdk");

          // Generate code that:
          // 1) "unwraps" the request (converts from the Dafny type to the AWS SDK type);
          // 2) calls boto3;
          // 3) wraps boto3 ClientErrors as Dafny failures
          writer.write(
            """
            boto_request_dict = $L
            try:
                boto_response_dict = self._impl.$L(**boto_request_dict)
            except ClientError as e:
                return Wrappers.Result_Failure(_sdk_error_to_dafny_error(e))
            """,
            input,
            codegenContext.symbolProvider().toSymbol(operationShape).getName()
          );

          Shape targetShape = codegenContext
            .model()
            .expectShape(operationShape.getOutputShape());
          // Generate code that converts the output from SDK type to the corresponding Dafny type
          String output = targetShape.accept(
            new AwsSdkToDafnyShapeVisitor(
              codegenContext,
              "boto_response_dict",
              writer
            )
          );

          // Generate code that wraps SDK success shapes as Dafny success shapes
          writer.write(
            """
            return Wrappers.Result_Success($L)
            """,
            SmithyNameResolver.isUnitShape(outputShape) ? "None" : output
          );
        }
      );
    }
  }
}
