package software.amazon.polymorph.smithypython.awssdk.customize;

import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.AwsSdkToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.awssdk.shapevisitor.DafnyToAwsSdkShapeVisitor;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file for AWS SDKs.
 * The shim wraps boto3 calls.
 * Its inputs are Dafny-modelled requests; its outputs are Dafny-modelled responses.
 * Internally, the shim will convert the Dafny-modelled requests
 *   to dictionaries passed to boto3 via kwargs,
 *   call boto3 with the request and receive a response,
 *   convert the boto3 response dictionary into a Dafny-modelled response,
 *   and return the Dafny-modelled response.
 * Other Dafny-generated Python code may use the shim to call AWS services (e.g. KMS, DDB).
 */
public class AwsSdkShimFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String typesModulePrelude = AwsSdkNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId());
    String moduleName = codegenContext.settings().getModuleName();
    codegenContext.writerDelegator().useFileWriter(moduleName + "/shim.py", "", writer -> {
      writer.write(
          """
          import Wrappers
          from botocore.exceptions import ClientError
          import $L
                          
          def sdk_error_to_dafny_error(e: ClientError):
              '''
              Converts the provided native Smithy-modelled error
              into the corresponding Dafny error.
              '''
              ${C|}
                          
          # TODO-Python: Typehint the shim class
          class $L:
              def __init__(self, _impl, _region):
                  self._impl = _impl
                  self._region = _region
                          
              ${C|}
              
              """, typesModulePrelude,
          writer.consumer(w -> generateAwsSdkErrorToDafnyErrorBlock(codegenContext, serviceShape, w)),
          AwsSdkNameResolver.shimForService(serviceShape),
          // TODO-Python: Uncomment to type out the shim class
          // typesModulePrelude, DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(serviceShape),
          writer.consumer(w -> generateOperationsBlock(codegenContext, serviceShape, w))
      );
    });
  }

  /**
   * Generate the method body for the `sdk_error_to_dafny_error` method.
   * This writes out a block to convert a boto3 ClientError modelled in JSON
   * into a Dafny-modelled error
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateAwsSdkErrorToDafnyErrorBlock(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    // Get modelled error converters for this service
    TreeSet<ShapeId> errorShapeSet = new TreeSet<ShapeId>(
        codegenContext.model().getStructureShapesWithTrait(ErrorTrait.class)
            .stream()
            .filter(structureShape -> structureShape.getId().getNamespace()
                .equals(codegenContext.settings().getService().getNamespace()))
            .map(Shape::getId)
            .collect(Collectors.toSet()));

    // First error case opens a new `if` block; others do not need to, and write `elif`
    boolean shouldOpenNewIfBlock = true;

    for (ShapeId errorShapeId : errorShapeSet) {
      // ex. for KMS.InvalidImportTokenException:
      // if e.response['Error']['Code'] == 'InvalidImportTokenException':
      //        return software_amazon_cryptography_services_kms_internaldafny_types.Error_InvalidImportTokenException(message=e.response['Error']['Code'])
      writer.openBlock(
          "$L e.response['Error']['Code'] == '$L':",
          "",
          shouldOpenNewIfBlock ? "if" : "elif",
          errorShapeId.getName(),
          () -> {
            writer.write("return $L.$L(message=e.response['Error']['Message'])",
                AwsSdkNameResolver.getDafnyPythonTypesModuleNameForShape(errorShapeId),
                DafnyNameResolver.getDafnyTypeForError(errorShapeId));
          }
      );
      shouldOpenNewIfBlock = false;
    }

    if (shouldOpenNewIfBlock) {
      // If `shouldOpenNewIfBlock` is true, then codegen never wrote any errors,
      // and this function should only cast to Opaque errors
      writer.write("""
        return $L.Error_Opaque(obj=e)
        """,
          AwsSdkNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId())
      );
    } else {
      // If `shouldOpenNewIfBlock` is false, then codegen wrote at least one error,
      // and this function should only cast to Opaque error if other `if` blocks were False
      writer.write("""
        else:
            return $L.Error_Opaque(obj=e)
        """,
          AwsSdkNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId())
      );
    }
  }

  /**
   * Generate shim methods for all operations in the SDK service shape.
   * Each method will take in a Dafny type as input and return a Dafny type as output.
   * Internally, each method will convert the Dafny input into a dictionary
   *   whose keys are boto3 API request parameters,
   *   call the boto3 client with the request dictionary mapped to its kwargs representation,
   *   receive a boto3 response,
   *   convert the response into its corresponding Dafny type,
   *   and return the Dafny type.
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateOperationsBlock(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext.model().expectShape(operationShapeId, OperationShape.class);

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      AwsSdkNameResolver.importDafnyTypeForAwsSdkShape(writer, inputShape, codegenContext);
      AwsSdkNameResolver.importDafnyTypeForAwsSdkShape(writer, outputShape, codegenContext);
      
      // Write the Shim operation block.
      // This takes in a Dafny input and returns a Dafny output.
      // This operation will:
      //  1) Convert the Dafny input to a Smithy-modelled input,
      //  2) Call the Smithy-generated client with the transformed input, and
      //  3) Convert the Smithy output to the Dafny type.
      writer.openBlock("def $L(self, $L) -> $L:", "",
          operationShape.getId().getName(),
          // Do not generate an `input` parameter if the operation does not take in an input
          Utils.isUnitShape(inputShape) ? "" : "input: " + DafnyNameResolver.getDafnyTypeForShape(inputShape),
          // Return `None` type if the operation does not return an output
          Utils.isUnitShape(outputShape) ? "None" : DafnyNameResolver.getDafnyTypeForShape(outputShape),
          () -> {

            Shape targetShapeInput = codegenContext.model().expectShape(operationShape.getInputShape());
            // Generate code that converts the input from the Dafny type to the corresponding Smithy type
            // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled output.
            // This has a side effect of possibly writing transformation code at the writer's current position.
            // For example, a service shape may require some calls to `ctor__()` after it is created,
            //   and cannot be constructed inline.
            // Polymorph will create an object representing the service's client, instantiate it,
            //   then reference that object in its `input` string.
            String input = targetShapeInput.accept(new DafnyToAwsSdkShapeVisitor(
                  codegenContext,
                  "input",
                  writer,
                  "shim"
              ));
            writer.addImport(".", "dafny_to_aws_sdk");

            // Generate code that:
            // 1) "unwraps" the request (converts from the Dafny type to the Smithy type),
            // 2) calls Smithy client,
            // 3) wraps Smithy failures as Dafny failures
            writer.write(
              """
              unwrapped_request = dafny_to_aws_sdk.$L
              try:
                  wrapped_response = self._impl.$L(**unwrapped_request)
              except ClientError as e:
                  return Wrappers.Result_Failure(sdk_error_to_dafny_error(e))
                  
              """,
              input,
              codegenContext.symbolProvider().toSymbol(operationShape).getName()
            );

            Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
            // Generate code that converts the output from SDK type to the corresponding Dafny type
            String output = targetShape.accept(new AwsSdkToDafnyShapeVisitor(
                codegenContext,
                "wrapped_response",
                writer,
                "shim"
            ));

            // Generate code that wraps SDK success shapes as Dafny success shapes
            writer.write(
                """
                return Wrappers.Result_Success($L)
                """,
                Utils.isUnitShape(outputShape) ? "None" : output
            );
          }
      );
    }
  }
}
